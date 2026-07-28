//===--- VPlace.h - Typed Layer 1 lvalue places ----------------*- C++ -*-===//
//
// A `VPlace` is a frontend/VCR lowering abstraction for the address of an
// lvalue. It owns the semantic address expression together with structured,
// ordered projections describing how that address was derived from a root
// object. Places are built by the AST converter and fully lowered to ordinary
// VLoad/VStore address expressions before passivization; they introduce no new
// Obligation sort and never change logic semantics.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_IR_VPLACE_H
#define LLVM_CLANG_VERIFY_IR_VPLACE_H

#include "VExpr.h"
#include "VType.h"
#include "clang/Basic/SourceLocation.h"
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace clang {
namespace verify {

enum class VProjectionKind { Deref, Field, Element };

/// One ordered step in deriving a place address from its root object. The
/// concrete dynamic index of an element projection lives in the place's address
/// expression; the projection records only the constant stride.
struct VPlaceProjection {
  VProjectionKind Kind = VProjectionKind::Deref;
  /// Field projection: source field name and exact byte offset.
  std::string FieldName;
  uint64_t OffsetBytes = 0;
  /// Element projection: element stride in target bytes.
  uint64_t StrideBytes = 0;
  SourceLocation Loc;
};

/// A typed lvalue place: an owned address expression plus the structured
/// projection chain used to build it.
class VPlace {
public:
  /// The semantic address expression (a pointer value). This is the dynamic
  /// representation consumed by VLoad/VStore once the place is lowered.
  std::unique_ptr<VExpr> Address;
  /// Type of the value stored at this place.
  VType ValueTy;
  SourceLocation Loc;
  /// Canonical identity of the root object type (empty for scalar roots).
  std::string RootTypeIdentity;
  /// Ordered projections from the root object to this place.
  std::vector<VPlaceProjection> Projections;

  VPlace() = default;
  VPlace(std::unique_ptr<VExpr> Base, VType ValueTy, SourceLocation Loc,
         std::string RootTypeIdentity = {})
      : Address(std::move(Base)), ValueTy(ValueTy), Loc(Loc),
        RootTypeIdentity(std::move(RootTypeIdentity)) {}

  explicit operator bool() const { return static_cast<bool>(Address); }

  /// Record a pointer dereference. The address is already the pointer value, so
  /// no arithmetic is applied.
  void applyDeref(SourceLocation L) {
    Projections.push_back(
        VPlaceProjection{VProjectionKind::Deref, {}, 0, 0, L});
  }

  /// Select a record field: address becomes `address + OffsetBytes`.
  void applyField(std::string Name, uint64_t OffsetBytes, SourceLocation L) {
    auto Offset = std::make_unique<VLiteralExpr>(
        static_cast<int64_t>(OffsetBytes), VType::makePtr(), L);
    Address =
        std::make_unique<VBinOpExpr>(VBinOp::Add, std::move(Address),
                                     std::move(Offset), VType::makePtr(), L);
    Projections.push_back(VPlaceProjection{VProjectionKind::Field,
                                           std::move(Name), OffsetBytes, 0, L});
  }

  /// Index an array/pointer: address becomes `address + ScaledIndex`, where
  /// `ScaledIndex` is the already-scaled byte offset (the semantic dynamic
  /// index representation).
  void applyElement(std::unique_ptr<VExpr> ScaledIndex, uint64_t StrideBytes,
                    SourceLocation L) {
    Address = std::make_unique<VBinOpExpr>(VBinOp::Add, std::move(Address),
                                           std::move(ScaledIndex),
                                           VType::makePtr(StrideBytes), L);
    Projections.push_back(
        VPlaceProjection{VProjectionKind::Element, {}, 0, StrideBytes, L});
  }

  const VExpr *address() const { return Address.get(); }

  /// Consume the place, yielding the lowered VLoad/VStore address expression.
  std::unique_ptr<VExpr> takeAddress() { return std::move(Address); }
};

} // namespace verify
} // namespace clang

#endif
