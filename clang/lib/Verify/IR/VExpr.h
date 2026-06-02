//===--- VExpr.h - Layer 1 expressions for CppVerify ------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VEXPR_H
#define LLVM_CLANG_VERIFY_IR_VEXPR_H

#include "VType.h"
#include "clang/Basic/SourceLocation.h"
#include <memory>
#include <string>

namespace clang {
namespace verify {

enum class VBinOp {
  Add, Sub, Mul, Div, Rem,
  Lt, Le, Gt, Ge, Eq, Ne,
  And, Or,
};

enum class VUnaryOp { Neg, Not };

class VExpr {
public:
  enum Kind {
    Literal, Var, BinOp, UnaryOp, Cast, Load, Result, Old, Conditional
  };

  Kind K;
  VType Ty;
  SourceLocation Loc;

  virtual ~VExpr() = default;

protected:
  VExpr(Kind K, VType Ty, SourceLocation Loc) : K(K), Ty(Ty), Loc(Loc) {}
};

class VLiteralExpr : public VExpr {
public:
  int64_t Value;
  VLiteralExpr(int64_t V, VType Ty, SourceLocation Loc)
      : VExpr(Literal, Ty, Loc), Value(V) {}
};

class VVarExpr : public VExpr {
public:
  std::string Name;
  VVarExpr(std::string Name, VType Ty, SourceLocation Loc)
      : VExpr(Var, Ty, Loc), Name(std::move(Name)) {}
};

class VBinOpExpr : public VExpr {
public:
  VBinOp Op;
  std::unique_ptr<VExpr> Lhs;
  std::unique_ptr<VExpr> Rhs;
  VBinOpExpr(VBinOp Op, std::unique_ptr<VExpr> L, std::unique_ptr<VExpr> R,
             VType Ty, SourceLocation Loc)
      : VExpr(BinOp, Ty, Loc), Op(Op), Lhs(std::move(L)), Rhs(std::move(R)) {}
};

class VUnaryOpExpr : public VExpr {
public:
  VUnaryOp Op;
  std::unique_ptr<VExpr> Operand;
  VUnaryOpExpr(VUnaryOp Op, std::unique_ptr<VExpr> O, VType Ty, SourceLocation Loc)
      : VExpr(UnaryOp, Ty, Loc), Op(Op), Operand(std::move(O)) {}
};

class VCastExpr : public VExpr {
public:
  VType FromTy;
  std::unique_ptr<VExpr> Inner;
  VCastExpr(std::unique_ptr<VExpr> I, VType From, VType To, SourceLocation Loc)
      : VExpr(Cast, To, Loc), FromTy(From), Inner(std::move(I)) {}
};

class VLoadExpr : public VExpr {
public:
  std::unique_ptr<VExpr> Ptr;
  VLoadExpr(std::unique_ptr<VExpr> P, VType Ty, SourceLocation Loc)
      : VExpr(Load, Ty, Loc), Ptr(std::move(P)) {}
};

class VResultExpr : public VExpr {
public:
  VResultExpr(VType Ty, SourceLocation Loc) : VExpr(Result, Ty, Loc) {}
};

class VOldExpr : public VExpr {
public:
  std::unique_ptr<VExpr> Inner;
  VOldExpr(std::unique_ptr<VExpr> I, VType Ty, SourceLocation Loc)
      : VExpr(Old, Ty, Loc), Inner(std::move(I)) {}
};

class VConditionalExpr : public VExpr {
public:
  std::unique_ptr<VExpr> Cond;
  std::unique_ptr<VExpr> Then;
  std::unique_ptr<VExpr> Else;
  VConditionalExpr(std::unique_ptr<VExpr> C, std::unique_ptr<VExpr> T,
                   std::unique_ptr<VExpr> E, VType Ty, SourceLocation Loc)
      : VExpr(Conditional, Ty, Loc), Cond(std::move(C)), Then(std::move(T)),
        Else(std::move(E)) {}
};

} // namespace verify
} // namespace clang

#endif