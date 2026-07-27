//===--- VExpr.h - Layer 1 expressions for CppVerify ------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VEXPR_H
#define LLVM_CLANG_VERIFY_IR_VEXPR_H

#include "VType.h"
#include "clang/Basic/SourceLocation.h"
#include <memory>
#include <string>

namespace clang {
namespace verify {

/// SSA name of the global heap array (versioned: __heap_0, __heap_1, ...).
inline constexpr const char *VHeapName = "__heap";
/// Address -> allocation identity map.
inline constexpr const char *VAllocationHeapName = "__heap_alloc";
/// Allocation identity -> base address map.
inline constexpr const char *VAllocationBaseHeapName = "__heap_alloc_base";
/// Allocation identity -> live/dead map.
inline constexpr const char *VLivenessHeapName = "__heap_live";
/// Allocation identity -> whether that identity has ever been issued.
inline constexpr const char *VAllocationUsedHeapName = "__heap_alloc_used";
/// Address -> initialized/uninitialized map.
inline constexpr const char *VInitializationHeapName = "__heap_init";
/// Allocation identity -> allocation size in target bytes.
inline constexpr const char *VAllocationSizeHeapName = "__heap_alloc_size";
/// Allocation identity -> required alignment in target bytes.
inline constexpr const char *VAllocationAlignHeapName = "__heap_alloc_align";

enum class VBinOp {
  Add,
  Sub,
  Mul,
  Div,
  Rem,
  BitAnd,
  BitOr,
  BitXor,
  Shl,
  Shr,
  Lt,
  Le,
  Gt,
  Ge,
  Eq,
  Ne,
  And,
  Or,
};

enum class VUnaryOp { Neg, Not, BitNot, ValidPtr, InitializedPtr };

/// Which signed-overflow predicate a VOverflowCheckExpr asserts the absence of.
enum class VOverflowOp { Add, Sub, Mul, Neg, SDiv };

class VExpr {
public:
  enum Kind {
    Literal,
    Var,
    BinOp,
    UnaryOp,
    Cast,
    Load,
    Result,
    Old,
    Conditional,
    Forall,
    Exists,
    HeapStore,
    FieldAccess,
    SpecCall,
    OverflowCheck
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
  std::string Value;
  VLiteralExpr(int64_t V, VType Ty, SourceLocation Loc)
      : VExpr(Literal, Ty, Loc), Value(std::to_string(V)) {}
  VLiteralExpr(std::string V, VType Ty, SourceLocation Loc)
      : VExpr(Literal, Ty, Loc), Value(std::move(V)) {}
};

class VVarExpr : public VExpr {
public:
  std::string Name;
  /// SSA companion carrying the lifetime identity of a local pointer value.
  std::string ProvenanceVariable;
  VVarExpr(std::string Name, VType Ty, SourceLocation Loc,
           std::string ProvenanceVariable = "")
      : VExpr(Var, Ty, Loc), Name(std::move(Name)),
        ProvenanceVariable(std::move(ProvenanceVariable)) {}
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
  std::string AllocationHeapVar;
  std::string LivenessHeapVar;
  std::string InitializationHeapVar;
  VUnaryOpExpr(VUnaryOp Op, std::unique_ptr<VExpr> O, VType Ty,
               SourceLocation Loc, std::string AllocationHeapVar = "",
               std::string LivenessHeapVar = "",
               std::string InitializationHeapVar = "")
      : VExpr(UnaryOp, Ty, Loc), Op(Op), Operand(std::move(O)),
        AllocationHeapVar(std::move(AllocationHeapVar)),
        LivenessHeapVar(std::move(LivenessHeapVar)),
        InitializationHeapVar(std::move(InitializationHeapVar)) {}
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
  std::string HeapVar;
  std::unique_ptr<VExpr> Ptr;
  VLoadExpr(std::unique_ptr<VExpr> P, VType Ty, SourceLocation Loc,
            std::string HeapVar = "")
      : VExpr(Load, Ty, Loc), HeapVar(std::move(HeapVar)), Ptr(std::move(P)) {}
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

class VQuantifiedExpr : public VExpr {
public:
  std::string Binder;
  VType BinderType;
  std::unique_ptr<VExpr> Lo;
  std::unique_ptr<VExpr> Hi;
  std::unique_ptr<VExpr> Body;
  VQuantifiedExpr(Kind K, std::string Binder, std::unique_ptr<VExpr> Lo,
                  std::unique_ptr<VExpr> Hi, std::unique_ptr<VExpr> Body,
                  SourceLocation Loc,
                  VType BinderType = VType::makeInt32(VIntMode::Machine))
      : VExpr(K, VType::makeBool(), Loc), Binder(std::move(Binder)),
        BinderType(BinderType), Lo(std::move(Lo)), Hi(std::move(Hi)),
        Body(std::move(Body)) {}
};

class VForallExpr : public VQuantifiedExpr {
public:
  VForallExpr(std::string Binder, std::unique_ptr<VExpr> Lo,
              std::unique_ptr<VExpr> Hi, std::unique_ptr<VExpr> Body,
              SourceLocation Loc,
              VType BinderType = VType::makeInt32(VIntMode::Machine))
      : VQuantifiedExpr(Forall, std::move(Binder), std::move(Lo), std::move(Hi),
                        std::move(Body), Loc, BinderType) {}
};

class VExistsExpr : public VQuantifiedExpr {
public:
  VExistsExpr(std::string Binder, std::unique_ptr<VExpr> Lo,
              std::unique_ptr<VExpr> Hi, std::unique_ptr<VExpr> Body,
              SourceLocation Loc,
              VType BinderType = VType::makeInt32(VIntMode::Machine))
      : VQuantifiedExpr(Exists, std::move(Binder), std::move(Lo), std::move(Hi),
                        std::move(Body), Loc, BinderType) {}
};

/// Passive heap update: HeapAfter == store(HeapBefore, Ptr, Val).
class VHeapStoreExpr : public VExpr {
public:
  std::string HeapBefore;
  std::string HeapAfter;
  std::unique_ptr<VExpr> Ptr;
  std::unique_ptr<VExpr> Val;
  VHeapStoreExpr(std::string Before, std::string After,
                 std::unique_ptr<VExpr> P, std::unique_ptr<VExpr> V,
                 SourceLocation Loc)
      : VExpr(HeapStore, VType::makeBool(), Loc), HeapBefore(std::move(Before)),
        HeapAfter(std::move(After)), Ptr(std::move(P)), Val(std::move(V)) {}
};

/// Struct field access: base.field (flattened to base.field in passivization).
class VFieldAccessExpr : public VExpr {
public:
  std::unique_ptr<VExpr> Base;
  std::string Field;
  VFieldAccessExpr(std::unique_ptr<VExpr> B, std::string Field, VType Ty,
                   SourceLocation Loc)
      : VExpr(FieldAccess, Ty, Loc), Base(std::move(B)),
        Field(std::move(Field)) {}
};

/// Call to a spec function (inlined or axiomatized during verification).
class VSpecCallExpr : public VExpr {
public:
  /// User-facing source name.
  std::string Callee;
  /// Signature-stable internal identity.
  std::string CalleeIdentity;
  std::vector<std::unique_ptr<VExpr>> Args;
  VSpecCallExpr(std::string Callee, std::string CalleeIdentity,
                std::vector<std::unique_ptr<VExpr>> Args, VType Ty,
                SourceLocation Loc)
      : VExpr(SpecCall, Ty, Loc), Callee(std::move(Callee)),
        CalleeIdentity(std::move(CalleeIdentity)), Args(std::move(Args)) {}
};

/// UB safety obligation: a boolean that is true iff the signed `Op` of its
/// operand(s) does NOT overflow. Generated by the UB-checking pass and lowered
/// to Z3's `bv*_no_overflow` primitives. `Rhs` is null for unary `Neg`.
class VOverflowCheckExpr : public VExpr {
public:
  VOverflowOp Op;
  std::unique_ptr<VExpr> Lhs;
  std::unique_ptr<VExpr> Rhs;
  VOverflowCheckExpr(VOverflowOp Op, std::unique_ptr<VExpr> L,
                     std::unique_ptr<VExpr> R, SourceLocation Loc)
      : VExpr(OverflowCheck, VType::makeBool(), Loc), Op(Op), Lhs(std::move(L)),
        Rhs(std::move(R)) {}
};

std::unique_ptr<VExpr> cloneVExpr(const VExpr *E);

/// Replace references to a quantifier binder with a concrete integer literal.
std::unique_ptr<VExpr> substituteBinderInVExpr(const VExpr *E,
                                               const std::string &Binder,
                                               int64_t Value, VIntMode Mode);

} // namespace verify
} // namespace clang

#endif