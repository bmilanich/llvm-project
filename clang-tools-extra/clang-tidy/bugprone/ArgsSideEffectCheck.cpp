//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ArgsSideEffectCheck.h"
#include "../utils/Matchers.h"
#include "../utils/OptionsUtils.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Lexer.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include <string>
#include <unordered_set>
#include <vector>

using namespace clang::ast_matchers;

template <> struct std::hash<std::pair<unsigned, unsigned>> {
  using argument_type = std::pair<unsigned, unsigned>;
  using result_type = std::size_t;
  result_type operator()(argument_type p) const {
    std::hash<unsigned> u;
    return u(p.first + u(p.second));
  }
};

namespace clang::tidy::bugprone {
namespace {
enum class ValueFor { Reading, Writing };
enum class ReferenceTo { Pointer, Object };

struct EffectRef {
  ReferenceTo to;
  const Expr *expr;
  EffectRef(ReferenceTo to_, const Expr *expr_) : to(to_), expr(expr_) {}
  EffectRef(EffectRef &&) noexcept = default;
  EffectRef &operator=(const EffectRef &) noexcept = default;
};

struct ArgDeps {
  using State = std::vector<EffectRef>;
  State reading;
  State writing;
  void read(const Expr *E, ReferenceTo ref = ReferenceTo::Pointer) {
    reading.emplace_back(ref, E);
  }
  void write(const Expr *E, ReferenceTo ref = ReferenceTo::Pointer) {
    writing.emplace_back(ref, E);
  }
};

template <typename T>
std::optional<std::pair<const T *, const T *>> cast2(const Expr *x,
                                                     const Expr *y) {
  const T *NewX = dyn_cast<T>(x);
  const T *NewY = dyn_cast<T>(y);
  if (NewX && NewY)
    return std::make_pair(NewX, NewY);
  else
    return std::nullopt;
}
template <typename Dest, typename T>
auto cast2(const std::pair<const T *, const T *> &p) {
  return cast2<Dest>(p.first, p.second);
}
template <typename T, typename F> auto call2(const std::pair<T, T> &x, F f) {
  return std::make_pair(f(x.first), f(x.second));
}
template <typename T> bool same(const std::pair<T, T> &x) {
  return x.first == x.second;
}
bool sameExpr(const Expr *x, const Expr *y) {
  if (x == nullptr || y == nullptr)
    return x == y;
  x = x->IgnoreParens();
  y = y->IgnoreParens();
  const auto SC = x->getStmtClass();
  if (y->getStmtClass() != SC) {
    return false;
  }
  if (dyn_cast<CXXThisExpr>(x)) {
    return true;
  }
  if (dyn_cast<MaterializeTemporaryExpr>(x)) {
    return false;
  }
  if (auto DRE = cast2<DeclRefExpr>(x, y); DRE) {
    const auto Value = call2(*DRE, [](auto p) { return p->getDecl(); });
    return same(Value);
  }

  if (auto ME = cast2<MemberExpr>(x, y); ME) {
    auto Value = call2(*ME, [](auto p) { return p->getMemberDecl(); });
    return same(Value);
  }
  if (auto Call = cast2<CallExpr>(x, y); Call) {
    auto Callee =
        call2(*Call, [](auto p) { return p->getCallee()->IgnoreImpCasts(); });
    if (auto DRE = cast2<DeclRefExpr>(Callee); DRE) {
      auto Decl = call2(*DRE, [](auto p) { return p->getDecl(); });
      if (!same(Decl)) {
        return false;
      } else {
        const unsigned N = Call->first->getNumArgs();
        for (unsigned i = 0; i != N; ++i) {
          auto Args = call2(
              *Call, [i](auto p) { return p->getArg(i)->IgnoreImpCasts(); });
          if (!sameExpr(Args.first, Args.second)) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }
  if (auto OpCall = cast2<CXXOperatorCallExpr>(x, y); OpCall) {
    auto OpKind = call2(*OpCall, [](auto p) { return p->getOperator(); });
    if (!same(OpKind)) {
      return false;
    }
    const unsigned N = OpCall->first->getNumArgs();
    for (unsigned i = 0; i != N; ++i) {
      auto Arg = call2(*OpCall, [i](auto p) { return p->getArg(i); });
      if (!sameExpr(Arg.first, Arg.second)) {
        return false;
      }
    }
    return true;
  }

  return false;
}
bool isConstExpr(const DeclRefExpr *DRE) {
  const ValueDecl *VD = DRE->getDecl();
  if (const auto *Var = dyn_cast<VarDecl>(VD)) {
    if (Var->isConstexpr() || Var->getType().isConstQualified()) {
      return true;
    } else {
      return false;
    }
  }
  if (dyn_cast<ValueDecl>(VD)) {
    return true;
  }
  return false;
}

bool intersectExpr(const EffectRef &r1, const EffectRef &r2) {
  auto x = r1.expr->IgnoreParens();
  auto y = r2.expr->IgnoreParens();
  const auto *MemX = dyn_cast<MemberExpr>(x);
  const auto *MemY = dyn_cast<MemberExpr>(y);
  if (MemX && MemY) {
    return sameExpr(MemX, MemY);
  } else if (MemX && r2.to == ReferenceTo::Object) {
    return sameExpr(MemX->getBase(), y);
  } else if (MemY && r1.to == ReferenceTo::Object) {
    return sameExpr(x, MemY->getBase());
  }
  return sameExpr(x, y);
}

void collectState(const Stmt *arg, ArgDeps &state,
                  ValueFor vf = ValueFor::Reading,
                  ReferenceTo ptr_ref = ReferenceTo::Pointer) {

  const auto *E = dyn_cast<Expr>(arg);
  if (E == nullptr) {
    // not an Expr, but might have Expr children
    for (const Stmt *Child : arg->children()) {
      if (Child)
        collectState(Child, state, vf);
    }
    return;
  }

  const auto *ME = dyn_cast<MemberExpr>(arg);
  const auto *DRE = dyn_cast<DeclRefExpr>(arg);

  if (DRE) {
    if (isConstExpr(DRE)) {
      return;
    }
    if (vf == ValueFor::Reading) {
      state.read(DRE, ptr_ref);
    } else {
      state.write(DRE, ptr_ref);
    }
    return;
  }

  if (ME) {
    if (vf == ValueFor::Reading) {
      state.read(E, ReferenceTo::Pointer);
    } else {
      state.write(E, ReferenceTo::Pointer);
    }
    if (ME) {
      // see if the base expression also touches the state
      collectState(ME->getBase()->IgnoreImpCasts(), state, ValueFor::Reading,
                   ReferenceTo::Pointer);
    }
    return;
  }
  if (const auto *Op = dyn_cast<UnaryOperator>(arg)) {
    UnaryOperator::Opcode OC = Op->getOpcode();
    const Expr *target = Op->getSubExpr();
    switch (OC) {
    case UO_PostInc:
    case UO_PostDec:
    case UO_PreInc:
    case UO_PreDec:
      collectState(target, state, ValueFor::Writing);
      break;
    case UO_AddrOf:
      collectState(target, state, vf);
      break;
    default:
      collectState(target, state, ValueFor::Reading);
    }
  }
  if (const auto *Op = dyn_cast<BinaryOperator>(arg)) {
    ValueFor lhs_vf = ValueFor::Reading;
    if (Op->isAssignmentOp()) {
      lhs_vf = ValueFor::Writing;
    }
    collectState(Op->getLHS(), state, lhs_vf);
    collectState(Op->getRHS(), state, ValueFor::Reading);
    return;
  }
  if (const auto *OpCallExpr = dyn_cast<CXXOperatorCallExpr>(arg)) {
    ValueFor lhs_vf = ValueFor::Reading;
    if (const auto *MethodDecl =
            dyn_cast_or_null<CXXMethodDecl>(OpCallExpr->getDirectCallee())) {
      if (!MethodDecl->isConst()) {

        OverloadedOperatorKind OpKind = OpCallExpr->getOperator();

        if (OpKind == OO_Equal || OpKind == OO_PlusEqual ||
            OpKind == OO_MinusEqual || OpKind == OO_StarEqual ||
            OpKind == OO_SlashEqual || OpKind == OO_AmpEqual ||
            OpKind == OO_PipeEqual || OpKind == OO_CaretEqual ||
            OpKind == OO_LessLessEqual || OpKind == OO_GreaterGreaterEqual ||
            OpKind == OO_LessLess || OpKind == OO_GreaterGreater ||
            OpKind == OO_PlusPlus || OpKind == OO_MinusMinus ||
            OpKind == OO_PercentEqual || OpKind == OO_New ||
            OpKind == OO_Delete || OpKind == OO_Array_New ||
            OpKind == OO_Array_Delete) {
          lhs_vf = ValueFor::Writing;
        }
      }
      const auto *BaseRef =
          dyn_cast<DeclRefExpr>(OpCallExpr->getArg(0)->IgnoreImpCasts());
      const ValueDecl *VD = BaseRef ? BaseRef->getDecl() : nullptr;
      if (const auto *Var = VD ? dyn_cast<VarDecl>(VD) : nullptr) {
        QualType T = Var->getType();
        if (const CXXRecordDecl *Record = T->getAsCXXRecordDecl()) {
          if (Record->isLambda() && MethodDecl->hasBody()) {
            // a lambda's operator() can modify enclosing state
            // even if the operator is const itself
            collectState(MethodDecl->getBody(), state, ValueFor::Reading);
          }
        }
      }
    }
    const auto NArgs = OpCallExpr->getNumArgs();
    collectState(OpCallExpr->getArg(0), state, lhs_vf, ReferenceTo::Object);
    for (unsigned i = 1; i < NArgs; ++i) {
      collectState(OpCallExpr->getArg(i), state, ValueFor::Reading);
    }
    return;
  }
  if (const auto *CExpr = dyn_cast<CallExpr>(arg)) {
    if (const auto *FuncDecl = CExpr->getDirectCallee()) {
      for (size_t I = 0; I < FuncDecl->getNumParams(); I++) {
        const ParmVarDecl *P = FuncDecl->getParamDecl(I);
        const Expr *ArgExpr =
            I < CExpr->getNumArgs() ? CExpr->getArg(I) : nullptr;
        const QualType PT = P->getType().getCanonicalType();
        ValueFor vf = ValueFor::Reading;
        if (ArgExpr) {
          if (!ArgExpr->isXValue() && PT->isReferenceType() &&
              !PT.getNonReferenceType().isConstQualified()) {
            vf = ValueFor::Writing;
          }
          collectState(ArgExpr, state, vf);
        }
      }
      if (const auto *MethodDecl = dyn_cast<CXXMethodDecl>(FuncDecl)) {
        bool is_const = MethodDecl->isConst() || MethodDecl->isConstexpr();
        if (const auto *MemCall = dyn_cast<CXXMemberCallExpr>(arg)) {
          const Expr *callee = MemCall->getCallee();
          if (const auto *ME = dyn_cast<MemberExpr>(callee)) {
            collectState(ME->getBase()->IgnoreImpCasts(), state,
                         is_const ? ValueFor::Reading : ValueFor::Writing,
                         ReferenceTo::Object);
          }
        }
      }
      return;
    }
    return;
  }

  if (dyn_cast<CXXThisExpr>(arg)) {
    switch (vf) {
    case ValueFor::Reading:
      state.read(E);
      break;
    case ValueFor::Writing:
      state.write(E);
      break;
    }
    return;
  }
  if (dyn_cast<LambdaExpr>(arg)) {
    // do not care about lambdas and if they pass through
    // the mutations in the body can cause a false positive
    return;
  }
  // otherwise just go through children
  for (const Stmt *Child : E->children()) {
    if (Child)
      collectState(Child, state, vf, ptr_ref);
  }
}
#if 0  
bool isNonConstRefType(const ParmVarDecl *P) {
  if (P) {
    const QualType PT = P->getType().getCanonicalType();
    if (const auto *PtrType = PT->getAs<PointerType>()) {
      return !PtrType->getPointeeType().isConstQualified();
    } else if (PT->isReferenceType()) {
      return !PT.getNonReferenceType().isConstQualified();
    }
  }
  return false;
}
#endif

template <typename T>
void debugDump(const T *expr, const PrintingPolicy &policy,
               const std::vector<ArgDeps> &state) {
  expr->printPretty(llvm::outs(), nullptr, policy);
  for (unsigned i = 0; i != state.size(); ++i) {
    llvm::outs() << "\nArg[" << i << "]\nread state:";
    for (const auto &x : state[i].reading) {
      x.expr->printPretty(llvm::outs(), nullptr, policy);
      llvm::outs() << " ";
    }
    llvm::outs() << "\nwrite state:";
    for (const auto &x : state[i].writing) {
      x.expr->printPretty(llvm::outs(), nullptr, policy);
      llvm::outs() << " ";
    }
  }
  llvm::outs() << "\n";
}
} // namespace

ArgsSideEffectCheck::ArgsSideEffectCheck(StringRef Name,
                                         ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context) {}

void ArgsSideEffectCheck::registerMatchers(MatchFinder *Finder) {
  Finder->addMatcher(stmt(anyOf(callExpr(hasArgument(1, expr())).bind("call"),
                                cxxConstructExpr(hasArgument(1, expr()),
                                                 unless(isListInitialization()))
                                    .bind("construct"))),
                     this);
}
void ArgsSideEffectCheck::check(const MatchFinder::MatchResult &Result) {
  std::vector<ArgDeps> state;
  SourceLocation Loc;
  auto policy = clang::PrintingPolicy(Result.Context->getLangOpts());

  if (const CallExpr *CE = Result.Nodes.getNodeAs<CallExpr>("call")) {

    Loc = CE->getExprLoc();
    unsigned sourceLine [[maybe_unused]] =
        Result.SourceManager->getSpellingLineNumber(Loc);

    const unsigned nargs = CE->getNumArgs();
    unsigned isMember = 0;
    // if it's a member operator call the object, whose member is called
    // will show up as the arg[0] and most likely will false positive so
    // I need to exclude it
    if (const auto *OpCallExpr = dyn_cast<CXXOperatorCallExpr>(CE)) {
      if (const auto *FD = OpCallExpr->getDirectCallee()) {
        isMember = (unsigned)FD->isCXXClassMember();
      }
    }
    state.reserve(nargs);
    for (unsigned i = isMember; i != nargs; ++i) {
      const Expr *Arg = CE->getArg(i)->IgnoreImpCasts();

      state.emplace_back();
      collectState(Arg, state[i - isMember], ValueFor::Reading);
    }
    // debugDump(CE, policy, state);

  } else if (const auto *CtrE =
                 Result.Nodes.getNodeAs<CXXConstructExpr>("construct")) {
    Loc = CtrE->getExprLoc();
    const unsigned nargs = CtrE->getNumArgs();
    state.reserve(nargs);
    for (unsigned i = 0; i != nargs; ++i) {
      const Expr *Arg = CtrE->getArg(i)->IgnoreImpCasts();
      state.emplace_back();
      collectState(Arg, state[i], ValueFor::Reading);
      // debugDump(CtrE, policy, state);
    }
  }
  auto greater = [policy](const EffectRef &x,
                          const EffectRef &y) -> const Expr * {
    std::string strX, strY;
    llvm::raw_string_ostream osX(strX), osY(strY);
    x.expr->printPretty(osX, nullptr, policy);
    y.expr->printPretty(osY, nullptr, policy);
    osX.flush();
    osY.flush();
    if (strX.size() < strY.size()) {
      return x.expr;
    } else {
      return y.expr;
    }
  };
  std::unordered_set<std::pair<unsigned, unsigned>> reported;

  auto normalized_pair = [](unsigned x, unsigned y) -> auto {
    if (x > y) {
      return std::make_pair(x, y);
    } else {
      return std::make_pair(y, x);
    }
  };

  auto report = [&](unsigned x, unsigned y) -> void {
    reported.insert(normalized_pair(x, y));
  };
  auto is_reported = [&](unsigned x, unsigned y) -> bool {
    return reported.find(normalized_pair(x, y)) != reported.end();
  };

  for (unsigned arg1 = 0; arg1 != state.size(); ++arg1) {
    for (unsigned arg2 = arg1 + 1; arg2 < state.size(); ++arg2) {

      for (const auto &r1 : state[arg1].reading) {
        for (const auto &w2 : state[arg2].writing) {
          if (intersectExpr(r1, w2) && !is_reported(arg1, arg2)) {
            const Expr *v = greater(r1, w2);
            QualType QT = v->getType();

            diag(Loc,
                 "value %3 %0 is read in the argument %1 and written in the "
                 "argument %2 ")
                << v << arg1 << arg2 << (QT->isPointerType() ? "at" : "of");
            report(arg1, arg2);
          }
        }
      }
      for (const auto &w1 : state[arg1].writing) {
        for (const auto &w2 : state[arg2].writing) {
          if (intersectExpr(w1, w2) && !is_reported(arg1, arg2)) {
            const Expr *v = greater(w1, w2);
            QualType QT = v->getType();
            diag(Loc, "value %3 %0 is written in the argument %1 and in the "
                      "argument %2")
                << v << arg1 << arg2 << (QT->isPointerType() ? "at" : "of");
          }
        }
      }
    }
  }
}

} // namespace clang::tidy::bugprone
