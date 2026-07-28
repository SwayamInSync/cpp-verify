//===--- VType.h - Layer 1 types for CppVerify ------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VTYPE_H
#define LLVM_CLANG_VERIFY_IR_VTYPE_H

#include "clang/Basic/SourceLocation.h"
#include <cstdint>
#include <string>
#include <vector>

namespace clang {
class ASTContext;
class QualType;
namespace verify {

enum class VIntMode { Math, Machine };

enum class VTypeKind {
  Void,
  Bool,
  Int32,
  Int64,
  Ptr,
  Struct,
  Array,
  Unsupported,
};

/// A source-type marker.
///
/// Scalar kinds (Bool, Int32, Int64, Ptr) carry the backend representation.
/// The aggregate marker kinds (Struct, Array) never reach the logic/backend
/// unchanged: they exist so the frontend can faithfully record a by-value
/// record or constant array and its target layout without embedding a
/// recursive layout graph. `TypeIdentity` is a stable, non-recursive canonical
/// identity used to associate a marker with its `VObjectLayout` entry.
struct VType {
  VTypeKind Kind = VTypeKind::Void;
  VIntMode IntMode = VIntMode::Machine;
  bool IsSigned = true;
  unsigned BitWidth = 32;
  uint64_t PointeeSizeBytes = 0;
  /// Target size/alignment of the aggregate object (Struct/Array markers).
  uint64_t ObjectSizeBytes = 0;
  uint64_t ObjectAlignBytes = 0;
  /// Constant-array element count and stride in target bytes (Array marker).
  uint64_t ArrayCount = 0;
  uint64_t ArrayStrideBytes = 0;
  /// Stable canonical identity of the aggregate type (Struct/Array markers).
  std::string TypeIdentity;

  static VType makeVoid() {
    return VType{VTypeKind::Void, VIntMode::Machine, true, 0};
  }
  static VType makeBool() {
    return VType{VTypeKind::Bool, VIntMode::Machine, false, 1};
  }
  static VType makeInt32(VIntMode M, bool IsSigned = true) {
    return VType{VTypeKind::Int32, M, IsSigned, 32};
  }
  static VType makeInt(VIntMode M, unsigned BitWidth, bool IsSigned = true) {
    return VType{BitWidth > 32 ? VTypeKind::Int64 : VTypeKind::Int32, M,
                 IsSigned, BitWidth};
  }
  static VType makePtr(uint64_t PointeeSizeBytes = 0) {
    VType Ty{VTypeKind::Ptr, VIntMode::Machine, false, 0};
    Ty.PointeeSizeBytes = PointeeSizeBytes;
    return Ty;
  }
  static VType makeStruct() {
    return VType{VTypeKind::Struct, VIntMode::Machine, false, 0};
  }
  static VType makeArray() {
    return VType{VTypeKind::Array, VIntMode::Machine, false, 0};
  }
  static VType makeUnsupported() {
    return VType{VTypeKind::Unsupported, VIntMode::Machine, false, 0};
  }

  bool isSignedInt() const {
    return (Kind == VTypeKind::Int32 || Kind == VTypeKind::Int64) && IsSigned;
  }

  bool isAggregate() const {
    return Kind == VTypeKind::Struct || Kind == VTypeKind::Array;
  }

  unsigned bvWidth() const { return BitWidth; }

  static VType fromQualType(QualType QT, VIntMode DefaultMode,
                            const ASTContext &Ctx);
};

/// Canonical representation equality. Pointer pointee sizes are source
/// metadata, but aggregate identities are part of their Layer 1 type.
inline bool sameRepresentation(const VType &L, const VType &R) {
  if (L.Kind != R.Kind || L.Kind == VTypeKind::Unsupported)
    return false;
  if (L.isAggregate())
    return L.TypeIdentity == R.TypeIdentity;
  if (L.Kind == VTypeKind::Int32 || L.Kind == VTypeKind::Int64)
    return L.IntMode == R.IntMode && L.IsSigned == R.IsSigned &&
           L.BitWidth == R.BitWidth;
  return true;
}

/// Stable canonical identity for an aggregate source type. Distinguishes
/// namespaces and types and is deterministic; never an unqualified display
/// name. Empty for scalar/pointer/void types.
std::string canonicalTypeIdentity(QualType QT, const ASTContext &Ctx);

enum class VObjectKind { Record, ConstantArray };

/// A compact array repetition dimension on a flattened leaf.
struct VObjectRepeat {
  uint64_t Count = 0;
  uint64_t StrideBytes = 0;
};

/// A single flattened scalar (or pointer) leaf of an aggregate layout.
struct VObjectLeaf {
  /// Full dotted/index path from the object root, e.g. ".next", "[*].first".
  std::string Path;
  /// Exact leaf type. Pointer leaves stay Ptr with PointeeSizeBytes and never
  /// recursively embed the pointee layout.
  VType Ty;
  uint64_t OffsetBytes = 0;
  uint64_t SizeBytes = 0;
  uint64_t AlignBytes = 0;
  /// Array dimensions represented by each `[*]` in Path, outermost first.
  /// This keeps arbitrarily large constant arrays exact without enumerating
  /// every element.
  std::vector<VObjectRepeat> Repeats;
  /// Field/element source location when available.
  SourceLocation Loc;
};

/// A canonical, copyable, non-recursive layout of a by-value record or
/// constant-array type. One entry exists per canonical type identity.
struct VObjectLayout {
  VObjectKind Kind = VObjectKind::Record;
  /// Canonical identity (matches the marker VType's TypeIdentity).
  std::string TypeIdentity;
  /// Human-readable canonical name for dumps.
  std::string DisplayName;
  uint64_t SizeBytes = 0;
  uint64_t AlignBytes = 0;
  /// Constant-array element count and stride (ConstantArray only).
  uint64_t ElementCount = 0;
  uint64_t StrideBytes = 0;
  /// Recursively flattened scalar/pointer leaves in offset order.
  std::vector<VObjectLeaf> Leaves;
};

} // namespace verify
} // namespace clang

#endif