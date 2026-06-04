//===--- VType.h - Layer 1 types for CppVerify ------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VTYPE_H
#define LLVM_CLANG_VERIFY_IR_VTYPE_H

namespace clang {
class QualType;
namespace verify {

enum class VIntMode { Math, Machine };

enum class VTypeKind {
  Void,
  Bool,
  Int32,
  Int64,
  Ptr,
};

struct VType {
  VTypeKind Kind = VTypeKind::Void;
  VIntMode IntMode = VIntMode::Machine;
  /// For integer kinds: true if the C++ type is unsigned. Unsigned overflow is
  /// defined (modular) in C++, so UB checking only instruments signed arithmetic.
  bool Unsigned = false;

  static VType makeVoid() { return VType{VTypeKind::Void, VIntMode::Machine}; }
  static VType makeBool() { return VType{VTypeKind::Bool, VIntMode::Machine}; }
  static VType makeInt32(VIntMode M) { return VType{VTypeKind::Int32, M}; }
  static VType makePtr() { return VType{VTypeKind::Ptr, VIntMode::Machine}; }

  /// Is this a signed integer kind (the only thing overflow checks apply to)?
  bool isSignedInt() const {
    return (Kind == VTypeKind::Int32 || Kind == VTypeKind::Int64) && !Unsigned;
  }

  static VType fromQualType(QualType QT, VIntMode DefaultMode);
};

} // namespace verify
} // namespace clang

#endif