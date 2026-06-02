//===--- VExpr.cpp --------------------------------------------------------===//
#include "VExpr.h"
#include "clang/AST/Type.h"

using namespace clang;
using namespace verify;

VType VType::fromQualType(QualType QT, VIntMode DefaultMode) {
  QT = QT.getCanonicalType();
  if (QT->isBooleanType())
    return VType::makeBool();
  if (QT->isVoidType())
    return VType::makeVoid();
  if (QT->isPointerType() || QT->isReferenceType())
    return VType::makePtr();
  if (QT->isIntegerType())
    return VType::makeInt32(DefaultMode);
  return VType::makeInt32(DefaultMode);
}