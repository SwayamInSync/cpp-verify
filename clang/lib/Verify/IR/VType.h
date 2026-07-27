//===--- VType.h - Layer 1 types for CppVerify ------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VTYPE_H
#define LLVM_CLANG_VERIFY_IR_VTYPE_H

#include <cstdint>

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
  Unsupported,
};

struct VType {
  VTypeKind Kind = VTypeKind::Void;
  VIntMode IntMode = VIntMode::Machine;
  bool IsSigned = true;
  unsigned BitWidth = 32;
  uint64_t PointeeSizeBytes = 0;

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
  static VType makeUnsupported() {
    return VType{VTypeKind::Unsupported, VIntMode::Machine, false, 0};
  }

  bool isSignedInt() const {
    return (Kind == VTypeKind::Int32 || Kind == VTypeKind::Int64) && IsSigned;
  }

  unsigned bvWidth() const { return BitWidth; }

  static VType fromQualType(QualType QT, VIntMode DefaultMode,
                            const ASTContext &Ctx);
};

} // namespace verify
} // namespace clang

#endif