//===--- ASTConverter.cpp -------------------------------------------------===//
#include "ASTConverter.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprContract.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/StmtContract.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <functional>
#include <iterator>

using namespace clang;
using namespace verify;

static std::string integerValueString(const llvm::APInt &Value, bool IsSigned) {
  llvm::SmallString<32> Buffer;
  Value.toString(Buffer, 10, IsSigned);
  return std::string(Buffer);
}

static std::string integerValueString(const llvm::APSInt &Value) {
  llvm::SmallString<32> Buffer;
  Value.toString(Buffer);
  return std::string(Buffer);
}

static std::unique_ptr<VExpr> scalePointerOffset(std::unique_ptr<VExpr> Offset,
                                                 uint64_t PointeeSize,
                                                 SourceLocation Loc) {
  if (!Offset || PointeeSize == 0 ||
      (Offset->Ty.Kind != VTypeKind::Int32 &&
       Offset->Ty.Kind != VTypeKind::Int64))
    return nullptr;

  VType SourceTy = Offset->Ty;
  VType MathTy = SourceTy;
  MathTy.IntMode = VIntMode::Math;
  if (SourceTy.IntMode != VIntMode::Math)
    Offset =
        std::make_unique<VCastExpr>(std::move(Offset), SourceTy, MathTy, Loc);
  if (PointeeSize == 1)
    return Offset;

  auto Stride =
      std::make_unique<VLiteralExpr>(std::to_string(PointeeSize), MathTy, Loc);
  return std::make_unique<VBinOpExpr>(VBinOp::Mul, std::move(Offset),
                                      std::move(Stride), MathTy, Loc);
}

static bool
isSupportedVerificationTypeImpl(QualType Ty,
                                llvm::SmallPtrSetImpl<const Type *> &Visiting) {
  if (Ty.isNull())
    return true;
  if (Ty.isVolatileQualified())
    return false;
  Ty = Ty.getCanonicalType().getUnqualifiedType();
  if (Ty->isFunctionType() || Ty->isVoidType() || Ty->isBooleanType() ||
      Ty->isIntegerType() || Ty->isEnumeralType() || Ty->isNullPtrType())
    return true;
  if (Ty->isReferenceType())
    return false;
  if (Ty->isPointerType()) {
    QualType Pointee = Ty->getPointeeType();
    if (Pointee->isVoidType())
      return true;
    if (Pointee->isPointerType() || Pointee->isReferenceType() ||
        Pointee->isFunctionType())
      return false;
    return isSupportedVerificationTypeImpl(Pointee, Visiting);
  }
  const auto *RT = Ty->getAs<RecordType>();
  if (!RT)
    return false;
  const RecordDecl *RD = RT->getDecl()->getDefinition();
  if (!RD || RD->isUnion())
    return false;
  if (const auto *CXXRD = dyn_cast<CXXRecordDecl>(RD))
    if (CXXRD->getNumBases() != 0 || CXXRD->isPolymorphic() ||
        !CXXRD->isTrivial() || !CXXRD->isStandardLayout())
      return false;
  if (!Visiting.insert(Ty.getTypePtr()).second)
    return true;
  for (const FieldDecl *Field : RD->fields())
    if (Field->isBitField() || Field->getType()->isRecordType() ||
        Field->getType()->isPointerType() ||
        Field->getType()->isReferenceType() ||
        !isSupportedVerificationTypeImpl(Field->getType(), Visiting)) {
      Visiting.erase(Ty.getTypePtr());
      return false;
    }
  Visiting.erase(Ty.getTypePtr());
  return true;
}

static bool isSupportedVerificationType(QualType Ty) {
  llvm::SmallPtrSet<const Type *, 8> Visiting;
  return isSupportedVerificationTypeImpl(Ty, Visiting);
}

static bool isSupportedReferenceParameter(QualType Ty) {
  if (Ty.isNull() || !Ty->isLValueReferenceType())
    return false;
  QualType Referent = Ty.getNonReferenceType();
  if (Referent.isVolatileQualified() || Referent->isAtomicType())
    return false;
  Referent = Referent.getCanonicalType().getUnqualifiedType();
  return Referent->isBooleanType() || Referent->isIntegerType() ||
         Referent->isEnumeralType();
}

static std::optional<std::string>
findUnsupportedType(const FunctionDecl *FD, bool AllowReferenceParameters) {
  if (!isSupportedVerificationType(FD->getReturnType()))
    return FD->getReturnType().getAsString();
  for (const ParmVarDecl *Param : FD->parameters()) {
    QualType Ty = Param->getType();
    if (Ty->isReferenceType()) {
      if (!AllowReferenceParameters || !isSupportedReferenceParameter(Ty))
        return Ty.getAsString();
    } else if (!isSupportedVerificationType(Ty)) {
      return Param->getType().getAsString();
    }
  }

  struct Finder : RecursiveASTVisitor<Finder> {
    std::optional<std::string> Found;
    bool AllowReferenceParameters;

    explicit Finder(bool AllowReferenceParameters)
        : AllowReferenceParameters(AllowReferenceParameters) {}

    bool VisitExpr(Expr *E) {
      if (const auto *ICE = dyn_cast<ImplicitCastExpr>(E))
        if (ICE->getCastKind() == CK_FunctionToPointerDecay)
          return true;
      if (!Found && !E->getType().isNull() &&
          !isSupportedVerificationType(E->getType()))
        Found = E->getType().getAsString();
      return !Found.has_value();
    }

    bool VisitVarDecl(VarDecl *D) {
      if (Found)
        return false;
      QualType Ty = D->getType();
      if (const auto *Param = dyn_cast<ParmVarDecl>(D);
          Param && Ty->isReferenceType() && AllowReferenceParameters &&
          isSupportedReferenceParameter(Ty))
        return true;
      if (!isSupportedVerificationType(Ty))
        Found = Ty.getAsString();
      return !Found.has_value();
    }
  } F(AllowReferenceParameters);
  if (FD->getBody())
    F.TraverseStmt(FD->getBody());
  return F.Found;
}

static bool hasIndirectMemoryAccess(const FunctionDecl *FD) {
  struct Finder : RecursiveASTVisitor<Finder> {
    bool Found = false;

    bool VisitUnaryOperator(UnaryOperator *U) {
      if (U->getOpcode() == UO_Deref)
        Found = true;
      return !Found;
    }

    bool VisitMemberExpr(MemberExpr *M) {
      if (M->isArrow())
        Found = true;
      return !Found;
    }

    bool VisitArraySubscriptExpr(ArraySubscriptExpr *) {
      Found = true;
      return false;
    }
  } F;
  if (FD->getBody())
    F.TraverseStmt(FD->getBody());
  return F.Found;
}

const FunctionContractInfo *
ASTConverter::functionContract(const FunctionDecl *FD) const {
  if (!FD)
    return nullptr;
  for (const FunctionDecl *Redecl : FD->redecls())
    if (const FunctionContractInfo *FCI = Ctx.getFunctionContract(Redecl))
      return FCI;
  return nullptr;
}

bool ASTConverter::calleeIsSpec(const FunctionDecl *FD) const {
  if (!FD)
    return false;
  if (const FunctionContractInfo *FCI = functionContract(FD))
    return FCI->IsSpec;
  return FD->isConstexpr() && FD->hasBody();
}

VIntMode ASTConverter::specCallIntMode(const FunctionDecl *FD) const {
  if (!FD)
    return VIntMode::Machine;
  if (const FunctionContractInfo *FCI = functionContract(FD))
    if (FCI->IsSpec)
      return VIntMode::Math;
  if (FD->isConstexpr())
    return VIntMode::Machine;
  return VIntMode::Math;
}

std::string ASTConverter::functionIdentity(const FunctionDecl *FD) {
  if (!FD)
    return {};
  FD = FD->getCanonicalDecl();
  if (auto It = FunctionIdentities.find(FD); It != FunctionIdentities.end())
    return It->second;

  std::string Mangled;
  llvm::raw_string_ostream OS(Mangled);
  std::unique_ptr<MangleContext> MC(Ctx.createMangleContext());
  if (MC->shouldMangleDeclName(FD))
    MC->mangleName(GlobalDecl(FD), OS);
  else
    OS << FD->getQualifiedNameAsString() << '\0'
       << FD->getType().getCanonicalType().getAsString();
  OS.flush();

  static constexpr char Hex[] = "0123456789abcdef";
  std::string Identity = "fn_";
  Identity.reserve(3 + Mangled.size() * 2);
  for (unsigned char C : Mangled) {
    Identity.push_back(Hex[C >> 4]);
    Identity.push_back(Hex[C & 0xf]);
  }
  FunctionIdentities.emplace(FD, Identity);
  return Identity;
}

std::string ASTConverter::specIdentityFromExpr(const Expr *E) {
  if (!E)
    return {};
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts()))
    if (const auto *FD = dyn_cast<FunctionDecl>(DRE->getDecl()))
      if (calleeIsSpec(FD))
        return functionIdentity(FD);
  return {};
}

bool ASTConverter::calleeIsProof(const FunctionDecl *FD) const {
  if (!FD)
    return false;
  if (const FunctionContractInfo *FCI = functionContract(FD))
    return FCI->IsProof;
  return false;
}

static QualType addressedType(const ParmVarDecl *P) {
  if (!P)
    return QualType();
  QualType T = P->getType();
  if (T->isReferenceType())
    return T.getNonReferenceType();
  if (T->isPointerType())
    return T->getPointeeType();
  return QualType();
}

static bool isMutableAddressParam(const ParmVarDecl *P) {
  QualType T = P->getType();
  if (T->isReferenceType())
    return !T.getNonReferenceType().isConstQualified();
  if (T->isPointerType())
    return !T->getPointeeType().isConstQualified();
  return false;
}

static bool aliasesListed(const FunctionContractInfo &FCI, StringRef A,
                          StringRef B) {
  for (const auto &Pair : FCI.Aliases) {
    const auto *L = dyn_cast<DeclRefExpr>(Pair.first->IgnoreParenImpCasts());
    const auto *R = dyn_cast<DeclRefExpr>(Pair.second->IgnoreParenImpCasts());
    if (!L || !R)
      continue;
    const auto *LD = dyn_cast<ParmVarDecl>(L->getDecl());
    const auto *RD = dyn_cast<ParmVarDecl>(R->getDecl());
    if (!LD || !RD)
      continue;
    if ((LD->getName() == A && RD->getName() == B) ||
        (LD->getName() == B && RD->getName() == A))
      return true;
  }
  return false;
}

static bool exprReferencesSpecCall(const VExpr *E, const std::string &Name) {
  if (!E)
    return false;
  switch (E->K) {
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    if (C->CalleeIdentity == Name)
      return true;
    for (const auto &Arg : C->Args)
      if (exprReferencesSpecCall(Arg.get(), Name))
        return true;
    return false;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return exprReferencesSpecCall(B->Lhs.get(), Name) ||
           exprReferencesSpecCall(B->Rhs.get(), Name);
  }
  case VExpr::UnaryOp:
    return exprReferencesSpecCall(
        static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Name);
  case VExpr::Cast:
    return exprReferencesSpecCall(
        static_cast<const VCastExpr *>(E)->Inner.get(), Name);
  case VExpr::Load:
    return exprReferencesSpecCall(static_cast<const VLoadExpr *>(E)->Ptr.get(),
                                  Name);
  case VExpr::Old:
    return exprReferencesSpecCall(static_cast<const VOldExpr *>(E)->Inner.get(),
                                  Name);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return exprReferencesSpecCall(C->Cond.get(), Name) ||
           exprReferencesSpecCall(C->Then.get(), Name) ||
           exprReferencesSpecCall(C->Else.get(), Name);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return exprReferencesSpecCall(Q->Lo.get(), Name) ||
           exprReferencesSpecCall(Q->Hi.get(), Name) ||
           exprReferencesSpecCall(Q->Body.get(), Name);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return exprReferencesSpecCall(H->Ptr.get(), Name) ||
           exprReferencesSpecCall(H->Val.get(), Name);
  }
  case VExpr::FieldAccess:
    return exprReferencesSpecCall(
        static_cast<const VFieldAccessExpr *>(E)->Base.get(), Name);
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return exprReferencesSpecCall(O->Lhs.get(), Name) ||
           exprReferencesSpecCall(O->Rhs.get(), Name);
  }
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return false;
  }
  return false;
}

static const RecordDecl *getRecordFromType(QualType T) {
  // See through references: a `C&`/`const C&` parameter's field access lowers
  // to the same "param.field" variable as a by-value `C`, so type_invariant
  // injection applies. Pointers are intentionally excluded: `p->field` lowers
  // to a heap Load, which the "param.field" substitution does not model.
  T = T.getNonReferenceType().getUnqualifiedType();
  if (const auto *RT = T->getAs<RecordType>())
    return RT->getDecl();
  return nullptr;
}

std::vector<std::string>
ASTConverter::trackedValueNames(const ValueDecl *D) const {
  std::vector<std::string> Names;
  if (!D)
    return Names;
  const std::string Base = valueName(D);
  if (const RecordDecl *RD = getRecordFromType(D->getType())) {
    if (const RecordDecl *Definition = RD->getDefinition())
      for (const FieldDecl *Field : Definition->fields())
        Names.push_back(Base + "." + Field->getNameAsString());
    return Names;
  }
  Names.push_back(Base);
  return Names;
}

std::string ASTConverter::valueName(const ValueDecl *D) const {
  if (const auto *P = dyn_cast_or_null<ParmVarDecl>(D))
    if (auto It = ParameterNames.find(P); It != ParameterNames.end())
      return It->second;
  return D ? D->getNameAsString() : std::string();
}

bool ASTConverter::referencesDynamicPointer(const Expr *E) const {
  if (!E)
    return false;
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts()))
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      if (DynamicPointers.count(VD))
        return true;
  for (const Stmt *Child : E->children())
    if (const auto *ChildExpr = dyn_cast_or_null<Expr>(Child))
      if (referencesDynamicPointer(ChildExpr))
        return true;
  return false;
}

const VarDecl *ASTConverter::directDynamicPointer(const Expr *E) const {
  if (!E)
    return nullptr;
  E = E->IgnoreParenImpCasts();
  const auto *DRE = dyn_cast<DeclRefExpr>(E);
  const auto *VD = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
  return VD && DynamicPointers.count(VD) ? VD : nullptr;
}

bool ASTConverter::dynamicPointerSourceTypesMatch(const VarDecl *Target,
                                                  const Expr *Source) const {
  if (!Target || !Source || !Target->getType()->isPointerType())
    return false;
  if (Source->isNullPointerConstant(Ctx, Expr::NPC_ValueDependentIsNotNull) !=
      Expr::NPCK_NotNull)
    return true;

  Source = Source->IgnoreParenImpCasts();
  if (const VarDecl *DirectSource = directDynamicPointer(Source))
    return Ctx.hasSameUnqualifiedType(
        Target->getType()->getPointeeType(),
        DirectSource->getType()->getPointeeType());
  if (const auto *C = dyn_cast<ConditionalOperator>(Source))
    return dynamicPointerSourceTypesMatch(Target, C->getTrueExpr()) &&
           dynamicPointerSourceTypesMatch(Target, C->getFalseExpr());
  return false;
}

std::unique_ptr<VExpr>
ASTConverter::convertDynamicPointerProvenance(const Expr *E) {
  if (!E)
    return nullptr;
  if (E->isNullPointerConstant(Ctx, Expr::NPC_ValueDependentIsNotNull) !=
      Expr::NPCK_NotNull)
    return std::make_unique<VLiteralExpr>(0, VType::makePtr(), E->getExprLoc());

  E = E->IgnoreParenImpCasts();
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E))
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      if (auto It = DynamicPointerProvenanceVariables.find(VD);
          It != DynamicPointerProvenanceVariables.end())
        return std::make_unique<VVarExpr>(It->second, VType::makePtr(),
                                          E->getExprLoc());

  if (const auto *C = dyn_cast<ConditionalOperator>(E)) {
    auto Cond = convertExpr(C->getCond());
    auto Then = convertDynamicPointerProvenance(C->getTrueExpr());
    auto Else = convertDynamicPointerProvenance(C->getFalseExpr());
    if (!Cond || !Then || !Else)
      return nullptr;
    return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(Then),
                                              std::move(Else), VType::makePtr(),
                                              E->getExprLoc());
  }
  return nullptr;
}

std::unique_ptr<VExpr>
ASTConverter::convertPointerDifferenceOperand(const Expr *E,
                                              uint64_t PointeeSize) {
  if (!E || PointeeSize == 0)
    return nullptr;
  E = E->IgnoreParenImpCasts();
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E))
    if (isa<VarDecl>(DRE->getDecl()) && E->getType()->isPointerType())
      return convertExpr(E);

  const auto *B = dyn_cast<BinaryOperator>(E);
  if (!B || (B->getOpcode() != BO_Add && B->getOpcode() != BO_Sub))
    return nullptr;

  const Expr *Pointer = nullptr;
  const Expr *Offset = nullptr;
  bool PointerOnLeft = B->getLHS()->getType()->isPointerType();
  if (PointerOnLeft) {
    Pointer = B->getLHS();
    Offset = B->getRHS();
  } else if (B->getOpcode() == BO_Add &&
             B->getRHS()->getType()->isPointerType()) {
    Pointer = B->getRHS();
    Offset = B->getLHS();
  } else {
    return nullptr;
  }

  const auto *PointerRef =
      dyn_cast<DeclRefExpr>(Pointer->IgnoreParenImpCasts());
  const auto *OffsetLiteral =
      dyn_cast<IntegerLiteral>(Offset->IgnoreParenImpCasts());
  if (!PointerRef || !isa<VarDecl>(PointerRef->getDecl()) || !OffsetLiteral ||
      OffsetLiteral->getValue().ugt(1) ||
      (B->getOpcode() == BO_Sub && !OffsetLiteral->getValue().isZero()))
    return nullptr;

  auto PointerValue = convertExpr(Pointer);
  auto OffsetValue = convertExpr(Offset);
  if (!PointerValue || !OffsetValue)
    return nullptr;
  OffsetValue =
      scalePointerOffset(std::move(OffsetValue), PointeeSize, E->getExprLoc());
  if (!OffsetValue)
    return nullptr;
  return std::make_unique<VBinOpExpr>(
      B->getOpcode() == BO_Sub ? VBinOp::Sub : VBinOp::Add,
      std::move(PointerValue), std::move(OffsetValue),
      VType::makePtr(PointeeSize), E->getExprLoc());
}

bool ASTConverter::appendDynamicPointerAssignment(
    const VarDecl *Target, const Expr *Source, SourceLocation Loc,
    std::vector<std::unique_ptr<VStmt>> &Out) {
  if (LoopDepth != 0) {
    Errors.push_back(CurrentFn->Name +
                     ": dynamic-storage pointer reassignment inside loops is "
                     "unsupported");
    return true;
  }
  if (!Target || !Source || !Target->getType()->isPointerType() ||
      !Source->getType()->isPointerType()) {
    Errors.push_back(CurrentFn->Name +
                     ": dynamic-storage pointer copies require matching "
                     "pointee types");
    return true;
  }

  auto Provenance = convertDynamicPointerProvenance(Source);
  if (!Provenance) {
    Errors.push_back(
        CurrentFn->Name +
        ": dynamic-storage pointer copies require direct, conditional, or "
        "null local sources");
    return true;
  }
  if (!dynamicPointerSourceTypesMatch(Target, Source)) {
    Errors.push_back(CurrentFn->Name +
                     ": dynamic-storage pointer copies require matching "
                     "pointee types");
    return true;
  }
  auto Value = convertExpr(Source);
  if (!Value)
    return true;

  auto It = DynamicPointerProvenanceVariables.find(Target);
  if (It == DynamicPointerProvenanceVariables.end())
    It = DynamicPointerProvenanceVariables
             .emplace(Target, "__cppverify_pointer_provenance_" +
                                  std::to_string(++DynamicProvenanceId))
             .first;
  DynamicPointers.insert(Target);

  const unsigned AssignmentId = ++DynamicPointerAssignmentId;
  const std::string ValueTemporary =
      "__cppverify_pointer_value_" + std::to_string(AssignmentId);
  const std::string ProvenanceTemporary =
      "__cppverify_pointer_provenance_value_" + std::to_string(AssignmentId);
  const VType PointerType =
      VType::fromQualType(Target->getType(), IntMode, Ctx);

  Out.push_back(
      std::make_unique<VAssignStmt>(ValueTemporary, std::move(Value), Loc));
  Out.push_back(std::make_unique<VAssignStmt>(ProvenanceTemporary,
                                              std::move(Provenance), Loc));
  Out.push_back(std::make_unique<VAssignStmt>(
      valueName(Target),
      std::make_unique<VVarExpr>(ValueTemporary, PointerType, Loc,
                                 ProvenanceTemporary),
      Loc));
  Out.push_back(std::make_unique<VAssignStmt>(
      It->second,
      std::make_unique<VVarExpr>(ProvenanceTemporary, VType::makePtr(), Loc),
      Loc));
  markInitialized(Target);
  return true;
}

bool ASTConverter::ghostAssignmentAllowed(const Expr *E) const {
  if (!InGhost)
    return true;
  if (!E)
    return false;
  E = E->IgnoreParenImpCasts();
  while (const auto *M = dyn_cast<MemberExpr>(E)) {
    if (M->isArrow())
      return false;
    E = M->getBase()->IgnoreParenImpCasts();
  }
  const auto *DRE = dyn_cast<DeclRefExpr>(E);
  const auto *VD = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
  return VD && GhostLocals.count(VD);
}

void ASTConverter::beginInitializationTracking(const FunctionDecl *FD) {
  DeclaredValueNames.clear();
  InitializedValues.clear();
  ReportedUninitializedValues.clear();
  DynamicPointers.clear();
  DynamicPointerProvenanceVariables.clear();
  GhostLocals.clear();
  DynamicProvenanceId = 0;
  DynamicPointerAssignmentId = 0;
  LoopDepth = 0;
  InitializationPathReachable = true;

  struct DynamicPointerDiscovery
      : RecursiveASTVisitor<DynamicPointerDiscovery> {
    std::set<const VarDecl *> Roots;
    std::vector<const VarDecl *> CandidateOrder;
    std::set<const VarDecl *> Candidates;
    std::vector<std::pair<const VarDecl *, const Expr *>> Assignments;

    void addCandidate(const VarDecl *Target) {
      if (Target && Target->isLocalVarDecl() &&
          Target->getType()->isPointerType() &&
          Candidates.insert(Target).second)
        CandidateOrder.push_back(Target);
    }

    bool VisitVarDecl(VarDecl *D) {
      if (!D->isLocalVarDecl() || !D->getType()->isPointerType() ||
          !D->hasInit())
        return true;
      addCandidate(D);
      if (isa<CXXNewExpr>(D->getInit()->IgnoreParenImpCasts()))
        Roots.insert(D);
      else
        Assignments.emplace_back(D, D->getInit());
      return true;
    }

    bool VisitBinaryOperator(BinaryOperator *B) {
      if (B->getOpcode() != BO_Assign)
        return true;
      const auto *DRE =
          dyn_cast<DeclRefExpr>(B->getLHS()->IgnoreParenImpCasts());
      const auto *Target = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
      if (!Target || !Target->isLocalVarDecl() ||
          !Target->getType()->isPointerType())
        return true;
      addCandidate(Target);
      Assignments.emplace_back(Target, B->getRHS());
      return true;
    }

    static bool referencesAny(const Expr *E,
                              const std::set<const VarDecl *> &Pointers) {
      if (!E)
        return false;
      if (const auto *DRE = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts()))
        if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
          if (Pointers.count(VD))
            return true;
      for (const Stmt *Child : E->children())
        if (const auto *ChildExpr = dyn_cast_or_null<Expr>(Child))
          if (referencesAny(ChildExpr, Pointers))
            return true;
      return false;
    }
  } Discovery;

  if (const Stmt *Body = FD->getBody())
    Discovery.TraverseStmt(const_cast<Stmt *>(Body));
  DynamicPointers = Discovery.Roots;
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (const auto &[Target, Source] : Discovery.Assignments)
      if (!DynamicPointers.count(Target) &&
          DynamicPointerDiscovery::referencesAny(Source, DynamicPointers))
        Changed |= DynamicPointers.insert(Target).second;
  }
  for (const VarDecl *Pointer : Discovery.CandidateOrder)
    if (DynamicPointers.count(Pointer))
      DynamicPointerProvenanceVariables.emplace(
          Pointer, "__cppverify_pointer_provenance_" +
                       std::to_string(++DynamicProvenanceId));

  for (const ParmVarDecl *P : FD->parameters()) {
    DeclaredValueNames.insert(valueName(P));
    for (const std::string &Name : trackedValueNames(P))
      InitializedValues.insert(Name);
  }
  TrackInitialization = true;
}

bool ASTConverter::requireInitialized(const ValueDecl *D,
                                      const FieldDecl *Field) {
  if (!TrackInitialization || !InitializationPathReachable || !D)
    return true;
  const std::string Base = valueName(D);
  if (!DeclaredValueNames.count(Base))
    return true;

  std::vector<std::string> Names;
  if (Field)
    Names.push_back(Base + "." + Field->getNameAsString());
  else
    Names = trackedValueNames(D);
  bool AllInitialized = true;
  for (const std::string &Name : Names) {
    if (InitializedValues.count(Name))
      continue;
    AllInitialized = false;
    if (ReportedUninitializedValues.insert(Name).second)
      Errors.push_back(CurrentFn->Name +
                       ": read of uninitialized local value: " + Name);
  }
  return AllInitialized;
}

void ASTConverter::markInitialized(const ValueDecl *D, const FieldDecl *Field) {
  if (!TrackInitialization || !InitializationPathReachable || !D)
    return;
  if (Field) {
    InitializedValues.insert(valueName(D) + "." + Field->getNameAsString());
    return;
  }
  for (const std::string &Name : trackedValueNames(D))
    InitializedValues.insert(Name);
}

static void collectInvariantFieldNames(const TypeContractInfo &TCI,
                                       llvm::StringSet<> &Out) {
  struct Collector : RecursiveASTVisitor<Collector> {
    llvm::StringSet<> &Out;
    explicit Collector(llvm::StringSet<> &O) : Out(O) {}
    bool VisitDeclRefExpr(DeclRefExpr *DRE) {
      if (const auto *FD = dyn_cast<FieldDecl>(DRE->getDecl()))
        Out.insert(FD->getNameAsString());
      return true;
    }
    bool VisitMemberExpr(MemberExpr *M) {
      if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl()))
        Out.insert(FD->getNameAsString());
      return true;
    }
  } C(Out);
  for (Expr *E : TCI.Invariants)
    C.TraverseStmt(E);
}

static bool
bodyReferencesInvariantFieldOnParam(const Stmt *S, const ParmVarDecl *P,
                                    const llvm::StringSet<> &InvFields) {
  struct Finder : RecursiveASTVisitor<Finder> {
    const ParmVarDecl *P;
    const llvm::StringSet<> &InvFields;
    bool Found = false;
    Finder(const ParmVarDecl *P, const llvm::StringSet<> &InvFields)
        : P(P), InvFields(InvFields) {}
    bool VisitMemberExpr(MemberExpr *M) {
      if (Found)
        return false;
      const auto *DRE =
          dyn_cast<DeclRefExpr>(M->getBase()->IgnoreParenImpCasts());
      if (!DRE || DRE->getDecl() != P)
        return true;
      if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl()))
        if (InvFields.contains(FD->getName()))
          Found = true;
      return true;
    }
  } F(P, InvFields);
  F.TraverseStmt(const_cast<Stmt *>(S));
  return F.Found;
}

void ASTConverter::injectTypeInvariants(const FunctionDecl *FD, VFunction &Fn) {
  const Stmt *Body = FD->getBody();
  if (!Body)
    return;
  for (const ParmVarDecl *P : FD->parameters()) {
    const RecordDecl *RD = getRecordFromType(P->getType());
    if (!RD)
      continue;
    const TypeContractInfo *TCI = Ctx.getTypeContract(RD);
    if (!TCI || TCI->Invariants.empty())
      continue;
    llvm::StringSet<> InvFields;
    collectInvariantFieldNames(*TCI, InvFields);
    if (InvFields.empty() ||
        !bodyReferencesInvariantFieldOnParam(Body, P, InvFields))
      continue;
    FieldSubstPrefix.clear();
    const auto *CXXRD = dyn_cast<CXXRecordDecl>(RD);
    if (!CXXRD)
      continue;
    for (const FieldDecl *Field : CXXRD->fields())
      FieldSubstPrefix[Field->getNameAsString()] = valueName(P) + ".";
    for (const Expr *Inv : TCI->Invariants) {
      if (auto VE = convertTypeInvariantExpr(Inv))
        Fn.Preconditions.push_back(std::move(VE));
    }
    FieldSubstPrefix.clear();
  }
}

std::unique_ptr<VExpr> ASTConverter::convertTypeInvariantExpr(const Expr *E) {
  bool SavedPost = InPost;
  bool SavedContract = InContractExpression;
  InPost = false;
  InContractExpression = true;
  auto Result = convertExpr(E);
  InPost = SavedPost;
  InContractExpression = SavedContract;
  return Result;
}

void ASTConverter::emitReturnInvariantAssert(
    const Expr *RetE, std::vector<std::unique_ptr<VStmt>> &Out,
    SourceLocation Loc) {
  if (!RetE)
    return;
  // Only a plain struct variable is handled (the common `return p;` form). The
  // invariant is checked over that variable's fields. Returning a struct wraps
  // the variable in copy-construction / materialization, so peel those (the
  // same unwrapping convertExpr performs) to reach the DeclRefExpr.
  const Expr *Cur = RetE->IgnoreParenImpCasts();
  while (true) {
    if (const auto *MTE = dyn_cast<MaterializeTemporaryExpr>(Cur))
      Cur = MTE->getSubExpr()->IgnoreParenImpCasts();
    else if (const auto *CE = dyn_cast<CXXConstructExpr>(Cur);
             CE && CE->getNumArgs() == 1)
      Cur = CE->getArg(0)->IgnoreParenImpCasts();
    else
      break;
  }
  const auto *DRE = dyn_cast<DeclRefExpr>(Cur);
  if (!DRE)
    return;
  const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
  if (!VD)
    return;
  const RecordDecl *RD = getRecordFromType(VD->getType());
  if (!RD)
    return;
  const TypeContractInfo *TCI = Ctx.getTypeContract(RD);
  if (!TCI || TCI->Invariants.empty())
    return;
  const auto *CXXRD = dyn_cast<CXXRecordDecl>(RD);
  if (!CXXRD)
    return;
  FieldSubstPrefix.clear();
  for (const FieldDecl *Field : CXXRD->fields())
    FieldSubstPrefix[Field->getNameAsString()] = valueName(VD) + ".";
  for (const Expr *Inv : TCI->Invariants)
    if (auto VE = convertTypeInvariantExpr(Inv))
      Out.push_back(std::make_unique<VContractAssertStmt>(std::move(VE), Loc));
  FieldSubstPrefix.clear();
}

static bool bodyReferencesFunction(const VFunction &Fn,
                                   const std::string &Identity) {
  std::function<bool(const std::vector<std::unique_ptr<VStmt>> &)> Contains =
      [&](const std::vector<std::unique_ptr<VStmt>> &Body) {
        for (const auto &S : Body) {
          switch (S->K) {
          case VStmt::Assign:
            if (exprReferencesSpecCall(
                    static_cast<const VAssignStmt &>(*S).Value.get(), Identity))
              return true;
            break;
          case VStmt::Store: {
            const auto &Store = static_cast<const VStoreStmt &>(*S);
            if (exprReferencesSpecCall(Store.Ptr.get(), Identity) ||
                exprReferencesSpecCall(Store.Value.get(), Identity))
              return true;
            break;
          }
          case VStmt::Allocate: {
            const auto &Allocate = static_cast<const VAllocateStmt &>(*S);
            if (exprReferencesSpecCall(Allocate.Initializer.get(), Identity))
              return true;
            break;
          }
          case VStmt::Free:
            if (exprReferencesSpecCall(
                    static_cast<const VFreeStmt &>(*S).Ptr.get(), Identity))
              return true;
            break;
          case VStmt::If: {
            const auto &I = static_cast<const VIfStmt &>(*S);
            if (exprReferencesSpecCall(I.Cond.get(), Identity) ||
                Contains(I.Then) || Contains(I.Else))
              return true;
            break;
          }
          case VStmt::While: {
            const auto &W = static_cast<const VWhileStmt &>(*S);
            if (exprReferencesSpecCall(W.Cond.get(), Identity) ||
                Contains(W.Body))
              return true;
            for (const auto &Dec : W.Decreases)
              if (exprReferencesSpecCall(Dec.get(), Identity))
                return true;
            for (const auto &Inv : W.Invariants)
              if (exprReferencesSpecCall(Inv.get(), Identity))
                return true;
            break;
          }
          case VStmt::Call: {
            const auto &C = static_cast<const VCallStmt &>(*S);
            if (C.CalleeIdentity == Identity)
              return true;
            for (const auto &Arg : C.Args)
              if (exprReferencesSpecCall(Arg.get(), Identity))
                return true;
            break;
          }
          case VStmt::Assert:
            if (exprReferencesSpecCall(
                    static_cast<const VAssertStmt &>(*S).Cond.get(), Identity))
              return true;
            break;
          case VStmt::Assume:
            if (exprReferencesSpecCall(
                    static_cast<const VAssumeStmt &>(*S).Cond.get(), Identity))
              return true;
            break;
          case VStmt::Return:
            if (exprReferencesSpecCall(
                    static_cast<const VReturnStmt &>(*S).Value.get(), Identity))
              return true;
            break;
          case VStmt::Seq:
            if (Contains(static_cast<const VSeqStmt &>(*S).Stmts))
              return true;
            break;
          case VStmt::GhostBlock:
            if (Contains(static_cast<const VGhostBlockStmt &>(*S).Body))
              return true;
            break;
          case VStmt::ContractAssert:
            if (exprReferencesSpecCall(
                    static_cast<const VContractAssertStmt &>(*S).Cond.get(),
                    Identity))
              return true;
            break;
          case VStmt::Havoc:
          case VStmt::RevealWithFuel:
          case VStmt::HideSpec:
          case VStmt::RevealSpec:
            break;
          }
        }
        return false;
      };
  return Contains(Fn.Body);
}

struct SpecBodyShape {
  bool Supported = true;
  bool AlwaysReturns = false;
};

static SpecBodyShape
analyzeSpecBody(const std::vector<std::unique_ptr<VStmt>> &Body) {
  for (const auto &Stmt : Body) {
    switch (Stmt->K) {
    case VStmt::Assign:
      continue;
    case VStmt::Return:
      return {static_cast<const VReturnStmt &>(*Stmt).Value != nullptr, true};
    case VStmt::If: {
      const auto &If = static_cast<const VIfStmt &>(*Stmt);
      SpecBodyShape Then = analyzeSpecBody(If.Then);
      SpecBodyShape Else =
          If.Else.empty() ? SpecBodyShape{} : analyzeSpecBody(If.Else);
      if (!Then.Supported || !Else.Supported)
        return {false, false};
      if (Then.AlwaysReturns && Else.AlwaysReturns)
        return {true, true};
      continue;
    }
    default:
      return {false, false};
    }
  }
  return {true, false};
}

static bool
specBodyCanBeAxiomatized(const std::vector<std::unique_ptr<VStmt>> &Body) {
  SpecBodyShape Shape = analyzeSpecBody(Body);
  return Shape.Supported && Shape.AlwaysReturns;
}

static void collectFunctionCandidates(const DeclContext *DC, ASTContext &Ctx,
                                      std::vector<const FunctionDecl *> &Out) {
  for (const Decl *D : DC->decls()) {
    if (const auto *NS = dyn_cast<NamespaceDecl>(D)) {
      collectFunctionCandidates(NS, Ctx, Out);
      continue;
    }
    if (const auto *LS = dyn_cast<LinkageSpecDecl>(D)) {
      collectFunctionCandidates(LS, Ctx, Out);
      continue;
    }
    if (const auto *RD = dyn_cast<RecordDecl>(D)) {
      if (RD->isCompleteDefinition())
        collectFunctionCandidates(RD, Ctx, Out);
      continue;
    }
    if (const auto *FTD = dyn_cast<FunctionTemplateDecl>(D)) {
      const FunctionDecl *FD = FTD->getTemplatedDecl();
      if (FD->isThisDeclarationADefinition())
        Out.push_back(FD);
      continue;
    }
    if (const auto *FD = dyn_cast<FunctionDecl>(D)) {
      if (FD->isThisDeclarationADefinition()) {
        Out.push_back(FD);
        continue;
      }
      const FunctionContractInfo *FCI = Ctx.getFunctionContract(FD);
      if (FCI && FCI->ContractDecl == FD && !FD->hasBody())
        Out.push_back(FD);
    }
  }
}

std::vector<std::unique_ptr<VFunction>> ASTConverter::convertTranslationUnit() {
  std::vector<std::unique_ptr<VFunction>> Out;
  llvm::StringSet<> Identities;
  std::vector<const FunctionDecl *> Definitions;
  collectFunctionCandidates(Ctx.getTranslationUnitDecl(), Ctx, Definitions);
  for (const FunctionDecl *FD : Definitions) {
    if (isa<CXXMethodDecl>(FD)) {
      if (functionContract(FD))
        Errors.push_back(FD->getNameAsString() +
                         ": member function verification is unsupported");
      continue;
    }
    if (FD->isTemplated()) {
      if (!FD->isInStdNamespace() &&
          Ctx.getSourceManager().isWrittenInMainFile(FD->getLocation()))
        Errors.push_back(FD->getNameAsString() +
                         ": function template verification is unsupported");
      continue;
    }
    if (FD->isInStdNamespace())
      continue;
    auto Fn = convertFunction(FD);
    if (Fn) {
      Identities.insert(Fn->Identity);
      Out.push_back(std::move(Fn));
    }
  }
  for (const FunctionDecl *FD : Definitions) {
    if (isa<CXXMethodDecl>(FD) || FD->isTemplated())
      continue;
    if (FD->isInStdNamespace() || Identities.contains(functionIdentity(FD)))
      continue;
    if (!FD->isConstexpr() || !FD->hasBody())
      continue;
    if (functionContract(FD))
      continue;
    auto Fn = convertConstexprSpec(FD);
    if (Fn) {
      Identities.insert(Fn->Identity);
      Out.push_back(std::move(Fn));
    }
  }
  std::map<std::string, std::set<std::string>> CallGraph;
  for (const auto &Fn : Out) {
    for (const auto &Target : Out)
      if (bodyReferencesFunction(*Fn, Target->Identity))
        CallGraph[Fn->Identity].insert(Target->Identity);
  }

  std::set<std::string> RequiresCallDefinedness;
  for (auto &Fn : Out)
    if (Fn->IsConstexprSpec) {
      Fn->RequiresCallDefinedness = true;
      RequiresCallDefinedness.insert(Fn->Identity);
    }
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (auto &Fn : Out) {
      if (!Fn->IsSpec || Fn->RequiresCallDefinedness)
        continue;
      for (const std::string &Callee : CallGraph[Fn->Identity])
        if (RequiresCallDefinedness.count(Callee)) {
          Fn->RequiresCallDefinedness = true;
          RequiresCallDefinedness.insert(Fn->Identity);
          Changed = true;
          break;
        }
    }
  }

  for (auto &Fn : Out) {
    bool MutuallyRecursive = false;
    for (const std::string &Next : CallGraph[Fn->Identity]) {
      if (Next == Fn->Identity)
        continue;
      std::set<std::string> Visited;
      std::function<bool(const std::string &)> ReachesSelf =
          [&](const std::string &Current) {
            if (!Visited.insert(Current).second)
              return false;
            for (const std::string &Successor : CallGraph[Current]) {
              if (Successor == Fn->Identity)
                return true;
              if (ReachesSelf(Successor))
                return true;
            }
            return false;
          };
      if (ReachesSelf(Next)) {
        MutuallyRecursive = true;
        break;
      }
    }
    if (MutuallyRecursive) {
      Errors.push_back(
          Fn->Name +
          (Fn->IsSpec || Fn->IsProof
               ? ": mutually recursive spec and proof functions are unsupported"
               : ": mutually recursive executable functions are unsupported"));
      continue;
    }
    bool Recursive = CallGraph[Fn->Identity].count(Fn->Identity) != 0;
    if (Recursive && Fn->Decreases.empty()) {
      Errors.push_back(
          Fn->Name +
          (Fn->IsSpec || Fn->IsProof
               ? ": recursive spec and proof functions require decreases"
               : ": recursive executable functions require decreases"));
      continue;
    }
    Fn->NeedsDecreasesCheck = Recursive;
  }
  return Out;
}

std::unique_ptr<VFunction>
ASTConverter::convertFunction(const FunctionDecl *FD) {
  const FunctionContractInfo *FCI = functionContract(FD);
  if (!FCI)
    return nullptr;
  ParameterNames.clear();
  const FunctionDecl *ContractDecl = FCI->ContractDecl ? FCI->ContractDecl : FD;
  if (ContractDecl->getNumParams() != FD->getNumParams()) {
    Errors.push_back(FD->getNameAsString() +
                     ": contract declaration parameter mismatch");
    return nullptr;
  }
  for (unsigned I = 0; I < FD->getNumParams(); ++I) {
    const ParmVarDecl *ContractParam = ContractDecl->getParamDecl(I);
    const ParmVarDecl *DefinitionParam = FD->getParamDecl(I);
    std::string Name = ContractParam->getNameAsString();
    if (Name.empty())
      Name = DefinitionParam->getNameAsString();
    if (Name.empty())
      Name = "__cppverify_param_" + std::to_string(I);
    ParameterNames[ContractParam] = Name;
    ParameterNames[DefinitionParam] = Name;
  }
  if (FD->isVariadic()) {
    Errors.push_back(FD->getNameAsString() +
                     ": variadic functions are unsupported");
    return nullptr;
  }
  if (FCI->IsSpec && FD->getReturnType()->isRecordType()) {
    Errors.push_back(FD->getNameAsString() +
                     ": aggregate-returning spec functions are unsupported");
    return nullptr;
  }
  if (FCI->IsSpec && hasIndirectMemoryAccess(FD)) {
    Errors.push_back(FD->getNameAsString() +
                     ": heap-reading spec functions are unsupported");
    return nullptr;
  }
  if (auto Unsupported =
          findUnsupportedType(FD, !FCI->IsSpec && !FCI->IsProof)) {
    Errors.push_back(FD->getNameAsString() +
                     ": unsupported C++ type in verification: " + *Unsupported);
    return nullptr;
  }

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  Fn->Identity = functionIdentity(FD);
  Fn->IsSpec = FCI->IsSpec;
  Fn->IsProof = FCI->IsProof;
  Fn->IsExternalContract = !FD->hasBody();
  if (Fn->IsExternalContract && (Fn->IsSpec || Fn->IsProof)) {
    Errors.push_back(Fn->Name +
                     ": spec and proof declarations require a definition");
    CurrentFn = nullptr;
    return nullptr;
  }
  IntMode = FCI->IsSpec ? VIntMode::Math : VIntMode::Machine;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode, Ctx);
  if (const RecordDecl *RD = getRecordFromType(FD->getReturnType()))
    if (const RecordDecl *Definition = RD->getDefinition())
      for (const FieldDecl *Field : Definition->fields())
        Fn->ReturnFields.emplace_back(
            Field->getNameAsString(),
            VType::fromQualType(Field->getType(), IntMode, Ctx));
  CurrentFn = Fn.get();
  InContractExpression = true;
  for (const Expr *D : FCI->Decreases)
    if (auto E = convertExpr(D))
      Fn->Decreases.push_back(std::move(E));
  InContractExpression = false;

  SmallVector<const ParmVarDecl *, 8> AddressParams;
  for (const ParmVarDecl *P : FD->parameters()) {
    if (const RecordDecl *RD = getRecordFromType(P->getType())) {
      if (const RecordDecl *Definition = RD->getDefinition())
        for (const FieldDecl *Field : Definition->fields())
          Fn->Params.emplace_back(
              valueName(P) + "." + Field->getNameAsString(),
              VType::fromQualType(Field->getType(), IntMode, Ctx));
    } else {
      Fn->Params.emplace_back(valueName(P),
                              VType::fromQualType(P->getType(), IntMode, Ctx));
    }
    QualType Addressed = addressedType(P);
    if (!Addressed.isNull() && !Addressed->isVoidType())
      AddressParams.push_back(P);
  }

  auto recordContractExpr = [&](const char *Clause, const Expr *E,
                                std::unique_ptr<VExpr> &Out) {
    if (!E)
      return;
    bool SavedContract = InContractExpression;
    InContractExpression = true;
    Out = convertExpr(E);
    InContractExpression = SavedContract;
    if (!Out)
      Errors.push_back(Fn->Name + ": unsupported expression in " + Clause);
  };

  InPost = false;
  for (const Expr *E : FCI->Preconditions) {
    std::unique_ptr<VExpr> PE;
    recordContractExpr("pre", E, PE);
    if (PE)
      Fn->Preconditions.push_back(std::move(PE));
  }
  Fn->ExplicitPreconditionCount =
      static_cast<unsigned>(Fn->Preconditions.size());
  InPost = true;
  for (const Expr *E : FCI->Postconditions) {
    std::unique_ptr<VExpr> PE;
    recordContractExpr("post", E, PE);
    if (PE)
      Fn->Postconditions.push_back(std::move(PE));
  }
  InPost = false;
  for (const Expr *E : FCI->Recommends) {
    std::unique_ptr<VExpr> RE;
    recordContractExpr("recommends", E, RE);
    if (RE)
      Fn->Recommends.push_back(std::move(RE));
  }
  for (const Expr *E : FCI->Modifies) {
    std::unique_ptr<VExpr> ME;
    recordContractExpr("modifies", E, ME);
    if (ME)
      Fn->Modifies.push_back(std::move(ME));
  }
  for (const auto &Pair : FCI->Aliases) {
    std::unique_ptr<VExpr> L;
    std::unique_ptr<VExpr> R;
    recordContractExpr("aliases", Pair.first, L);
    recordContractExpr("aliases", Pair.second, R);
    if (L && R)
      Fn->Aliases.emplace_back(std::move(L), std::move(R));
  }
  InPost = false;

  if (!Fn->IsSpec) {
    for (const ParmVarDecl *P : AddressParams) {
      auto Pointer = std::make_unique<VVarExpr>(valueName(P), VType::makePtr(),
                                                SourceLocation());
      auto IsNull = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, cloneVExpr(Pointer.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), SourceLocation()),
          VType::makeBool(), SourceLocation());
      auto IsValid =
          std::make_unique<VUnaryOpExpr>(VUnaryOp::ValidPtr, std::move(Pointer),
                                         VType::makeBool(), SourceLocation());
      auto IsInitialized = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::InitializedPtr,
          std::make_unique<VVarExpr>(valueName(P), VType::makePtr(),
                                     SourceLocation()),
          VType::makeBool(), SourceLocation());
      auto Readable = std::make_unique<VBinOpExpr>(
          VBinOp::And, std::move(IsValid), std::move(IsInitialized),
          VType::makeBool(), SourceLocation());
      if (P->getType()->isReferenceType()) {
        auto NonNull =
            std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(IsNull),
                                           VType::makeBool(), SourceLocation());
        Fn->Preconditions.push_back(std::make_unique<VBinOpExpr>(
            VBinOp::And, std::move(NonNull), std::move(Readable),
            VType::makeBool(), SourceLocation()));
      } else {
        Fn->Preconditions.push_back(std::make_unique<VBinOpExpr>(
            VBinOp::Or, std::move(IsNull), std::move(Readable),
            VType::makeBool(), SourceLocation()));
      }
    }
    QualType ReturnType = FD->getReturnType();
    if (ReturnType->isPointerType() &&
        !ReturnType->getPointeeType()->isVoidType()) {
      auto Result =
          std::make_unique<VResultExpr>(VType::makePtr(), SourceLocation());
      auto IsNull = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, cloneVExpr(Result.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), SourceLocation()),
          VType::makeBool(), SourceLocation());
      auto IsValid =
          std::make_unique<VUnaryOpExpr>(VUnaryOp::ValidPtr, std::move(Result),
                                         VType::makeBool(), SourceLocation());
      auto IsInitialized = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::InitializedPtr,
          std::make_unique<VResultExpr>(VType::makePtr(), SourceLocation()),
          VType::makeBool(), SourceLocation());
      auto Readable = std::make_unique<VBinOpExpr>(
          VBinOp::And, std::move(IsValid), std::move(IsInitialized),
          VType::makeBool(), SourceLocation());
      Fn->Postconditions.push_back(std::make_unique<VBinOpExpr>(
          VBinOp::Or, std::move(IsNull), std::move(Readable), VType::makeBool(),
          SourceLocation()));
    }
  }

  // A mutable address parameter has exclusive access to its complete object.
  for (unsigned I = 0; I < AddressParams.size(); ++I) {
    for (unsigned J = I + 1; J < AddressParams.size(); ++J) {
      if (!isMutableAddressParam(AddressParams[I]) &&
          !isMutableAddressParam(AddressParams[J]))
        continue;
      const bool MayAlias = aliasesListed(*FCI, valueName(AddressParams[I]),
                                          valueName(AddressParams[J]));
      QualType PointeeI = addressedType(AddressParams[I]).getUnqualifiedType();
      QualType PointeeJ = addressedType(AddressParams[J]).getUnqualifiedType();
      if (MayAlias && !Ctx.hasSameType(PointeeI, PointeeJ)) {
        Errors.push_back(
            Fn->Name +
            ": aliases between different pointee types are unsupported");
        continue;
      }
      auto Ptr = [&](const ParmVarDecl *P) {
        return std::make_unique<VVarExpr>(valueName(P), VType::makePtr(),
                                          SourceLocation());
      };
      auto Null = [] {
        return std::make_unique<VLiteralExpr>(0, VType::makePtr(),
                                              SourceLocation());
      };
      auto ANull = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, Ptr(AddressParams[I]), Null(), VType::makeBool(),
          SourceLocation());
      auto BNull = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, Ptr(AddressParams[J]), Null(), VType::makeBool(),
          SourceLocation());
      auto EitherNull = std::make_unique<VBinOpExpr>(
          VBinOp::Or, std::move(ANull), std::move(BNull), VType::makeBool(),
          SourceLocation());

      auto End = [&](const ParmVarDecl *P, QualType Pointee) {
        auto Size = std::make_unique<VLiteralExpr>(
            std::to_string(Ctx.getTypeSizeInChars(Pointee).getQuantity()),
            VType::makePtr(), SourceLocation());
        return std::make_unique<VBinOpExpr>(VBinOp::Add, Ptr(P),
                                            std::move(Size), VType::makePtr(),
                                            SourceLocation());
      };
      auto IBeforeJ = std::make_unique<VBinOpExpr>(
          VBinOp::Le, End(AddressParams[I], PointeeI), Ptr(AddressParams[J]),
          VType::makeBool(), SourceLocation());
      auto JBeforeI = std::make_unique<VBinOpExpr>(
          VBinOp::Le, End(AddressParams[J], PointeeJ), Ptr(AddressParams[I]),
          VType::makeBool(), SourceLocation());
      std::unique_ptr<VExpr> Relation = std::make_unique<VBinOpExpr>(
          VBinOp::Or, std::move(IBeforeJ), std::move(JBeforeI),
          VType::makeBool(), SourceLocation());
      if (MayAlias) {
        auto Same = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, Ptr(AddressParams[I]), Ptr(AddressParams[J]),
            VType::makeBool(), SourceLocation());
        Relation = std::make_unique<VBinOpExpr>(
            VBinOp::Or, std::move(Same), std::move(Relation), VType::makeBool(),
            SourceLocation());
      }
      Fn->Preconditions.push_back(std::make_unique<VBinOpExpr>(
          VBinOp::Or, std::move(EitherNull), std::move(Relation),
          VType::makeBool(), SourceLocation()));
    }
  }

  if (const Stmt *Body = FD->getBody()) {
    injectTypeInvariants(FD, *Fn);
    beginInitializationTracking(FD);
    Fn->Body = convertStmt(Body);
    TrackInitialization = false;
    if (!DynamicPointerProvenanceVariables.empty()) {
      std::vector<std::pair<std::string, SourceLocation>> InitialProvenance;
      InitialProvenance.reserve(DynamicPointerProvenanceVariables.size());
      for (const auto &[Pointer, Provenance] :
           DynamicPointerProvenanceVariables)
        InitialProvenance.emplace_back(Provenance, Pointer->getBeginLoc());
      std::sort(InitialProvenance.begin(), InitialProvenance.end(),
                [](const auto &L, const auto &R) { return L.first < R.first; });

      std::vector<std::unique_ptr<VStmt>> InitializedBody;
      InitializedBody.reserve(InitialProvenance.size() + Fn->Body.size());
      for (const auto &[Provenance, Loc] : InitialProvenance)
        InitializedBody.push_back(std::make_unique<VAssignStmt>(
            Provenance,
            std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc), Loc));
      for (auto &S : Fn->Body)
        InitializedBody.push_back(std::move(S));
      Fn->Body = std::move(InitializedBody);
    }
    if (Fn->IsSpec && !specBodyCanBeAxiomatized(Fn->Body)) {
      Errors.push_back(Fn->Name +
                       ": spec function body is unsupported by axiomatic "
                       "lowering");
      CurrentFn = nullptr;
      return nullptr;
    }
    if (!Fn->IsSpec && Fn->Body.empty() && Fn->Postconditions.empty()) {
      CurrentFn = nullptr;
      return nullptr;
    }
  }
  if (Fn->IsSpec && Fn->Body.empty() && Fn->Decreases.empty()) {
    CurrentFn = nullptr;
    return nullptr;
  }
  CurrentFn = nullptr;
  return Fn;
}

std::unique_ptr<VFunction>
ASTConverter::convertConstexprSpec(const FunctionDecl *FD) {
  ParameterNames.clear();
  if (hasIndirectMemoryAccess(FD))
    return nullptr;
  if (!FD->isConstexpr() || !FD->hasBody())
    return nullptr;
  if (FD->getReturnType()->isRecordType()) {
    Errors.push_back(FD->getNameAsString() +
                     ": aggregate-returning constexpr specs are unsupported");
    return nullptr;
  }
  if (auto Unsupported = findUnsupportedType(FD, false)) {
    Errors.push_back(FD->getNameAsString() +
                     ": unsupported C++ type in verification: " + *Unsupported);
    return nullptr;
  }

  auto Fn = std::make_unique<VFunction>();
  Fn->Name = FD->getNameAsString();
  Fn->Identity = functionIdentity(FD);
  Fn->IsSpec = true;
  Fn->IsConstexprSpec = true;
  IntMode = VIntMode::Machine;
  Fn->IntMode = IntMode;
  Fn->ReturnType = VType::fromQualType(FD->getReturnType(), IntMode, Ctx);
  CurrentFn = Fn.get();

  for (const ParmVarDecl *P : FD->parameters()) {
    if (const RecordDecl *RD = getRecordFromType(P->getType())) {
      if (const RecordDecl *Definition = RD->getDefinition())
        for (const FieldDecl *Field : Definition->fields())
          Fn->Params.emplace_back(
              P->getNameAsString() + "." + Field->getNameAsString(),
              VType::fromQualType(Field->getType(), IntMode, Ctx));
    } else {
      Fn->Params.emplace_back(P->getNameAsString(),
                              VType::fromQualType(P->getType(), IntMode, Ctx));
    }
  }

  if (const Stmt *Body = FD->getBody()) {
    beginInitializationTracking(FD);
    Fn->Body = convertStmt(Body);
    TrackInitialization = false;
  }
  if (Fn->Body.empty()) {
    CurrentFn = nullptr;
    return nullptr;
  }
  CurrentFn = nullptr;
  return Fn;
}

std::optional<VBinOp> ASTConverter::convertBinOpcode(BinaryOperatorKind Op) {
  switch (Op) {
  case BO_LT:
    return VBinOp::Lt;
  case BO_LE:
    return VBinOp::Le;
  case BO_GT:
    return VBinOp::Gt;
  case BO_GE:
    return VBinOp::Ge;
  case BO_EQ:
    return VBinOp::Eq;
  case BO_NE:
    return VBinOp::Ne;
  case BO_Add:
    return VBinOp::Add;
  case BO_Sub:
    return VBinOp::Sub;
  case BO_Mul:
    return VBinOp::Mul;
  case BO_Div:
    return VBinOp::Div;
  case BO_Rem:
    return VBinOp::Rem;
  case BO_And:
    return VBinOp::BitAnd;
  case BO_Or:
    return VBinOp::BitOr;
  case BO_Xor:
    return VBinOp::BitXor;
  case BO_Shl:
    return VBinOp::Shl;
  case BO_Shr:
    return VBinOp::Shr;
  case BO_LAnd:
    return VBinOp::And;
  case BO_LOr:
    return VBinOp::Or;
  default:
    return std::nullopt;
  }
}

std::unique_ptr<VExpr>
ASTConverter::convertArrowFieldAddress(const MemberExpr *M) {
  if (!M)
    return nullptr;
  const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl());
  if (!FD || FD->isBitField())
    return nullptr;
  const Expr *Pointer = nullptr;
  if (M->isArrow()) {
    Pointer = M->getBase();
  } else {
    const auto *Deref =
        dyn_cast<UnaryOperator>(M->getBase()->IgnoreParenImpCasts());
    if (Deref && Deref->getOpcode() == UO_Deref)
      Pointer = Deref->getSubExpr();
  }
  if (!Pointer)
    return nullptr;
  if (referencesDynamicPointer(Pointer)) {
    Errors.push_back(CurrentFn->Name +
                     ": dynamic-storage pointers cannot select record fields");
    return nullptr;
  }
  auto Base = convertExpr(Pointer);
  if (!Base)
    return nullptr;

  const RecordDecl *Parent = FD->getParent();
  unsigned FieldIndex = 0;
  for (const FieldDecl *Field : Parent->fields()) {
    if (Field == FD)
      break;
    ++FieldIndex;
  }
  uint64_t BitOffset =
      Ctx.getASTRecordLayout(Parent).getFieldOffset(FieldIndex);
  if (BitOffset % Ctx.getCharWidth() != 0)
    return nullptr;
  uint64_t ByteOffset = BitOffset / Ctx.getCharWidth();
  auto Offset = std::make_unique<VLiteralExpr>(
      static_cast<int64_t>(ByteOffset), VType::makePtr(), M->getExprLoc());
  return std::make_unique<VBinOpExpr>(VBinOp::Add, std::move(Base),
                                      std::move(Offset), VType::makePtr(),
                                      M->getExprLoc());
}

std::unique_ptr<VExpr> ASTConverter::convertLValueAddress(const Expr *E) {
  if (!E)
    return nullptr;
  E = E->IgnoreParens();
  while (const auto *Cast = dyn_cast<ImplicitCastExpr>(E)) {
    if (Cast->getCastKind() != CK_NoOp)
      return nullptr;
    E = Cast->getSubExpr()->IgnoreParens();
  }

  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
    if (!VD || !isa<ParmVarDecl>(VD) || !VD->getType()->isLValueReferenceType())
      return nullptr;
    requireInitialized(VD);
    return std::make_unique<VVarExpr>(
        valueName(VD), VType::fromQualType(VD->getType(), IntMode, Ctx),
        E->getExprLoc());
  }

  if (const auto *U = dyn_cast<UnaryOperator>(E);
      U && U->getOpcode() == UO_Deref) {
    const Expr *Pointer = U->getSubExpr()->IgnoreParenImpCasts();
    const auto *PointerRef = dyn_cast<DeclRefExpr>(Pointer);
    const auto *PointerVar =
        PointerRef ? dyn_cast<VarDecl>(PointerRef->getDecl()) : nullptr;
    if (!PointerVar || !PointerVar->getType()->isPointerType())
      return nullptr;
    if (referencesDynamicPointer(U->getSubExpr()) &&
        !directDynamicPointer(U->getSubExpr())) {
      Errors.push_back(CurrentFn->Name +
                       ": dynamic-storage reference binding requires its "
                       "direct allocation pointer");
      return nullptr;
    }
    return convertExpr(U->getSubExpr());
  }

  return nullptr;
}

std::unique_ptr<VExpr>
ASTConverter::convertRecordField(std::unique_ptr<VExpr> Base,
                                 const FieldDecl *Field, SourceLocation Loc) {
  if (!Base || !Field)
    return nullptr;
  VType Ty = VType::fromQualType(Field->getType(), IntMode, Ctx);
  if (Base->K == VExpr::Var || Base->K == VExpr::Result)
    return std::make_unique<VFieldAccessExpr>(
        std::move(Base), Field->getNameAsString(), Ty, Loc);
  if (Base->K == VExpr::Conditional) {
    auto Conditional = std::unique_ptr<VConditionalExpr>(
        static_cast<VConditionalExpr *>(Base.release()));
    auto Then = convertRecordField(std::move(Conditional->Then), Field, Loc);
    auto Else = convertRecordField(std::move(Conditional->Else), Field, Loc);
    if (!Then || !Else)
      return nullptr;
    return std::make_unique<VConditionalExpr>(std::move(Conditional->Cond),
                                              std::move(Then), std::move(Else),
                                              Ty, Loc);
  }
  if (Base->K == VExpr::Old) {
    auto Old =
        std::unique_ptr<VOldExpr>(static_cast<VOldExpr *>(Base.release()));
    auto Inner = convertRecordField(std::move(Old->Inner), Field, Loc);
    if (!Inner)
      return nullptr;
    return std::make_unique<VOldExpr>(std::move(Inner), Ty, Loc);
  }
  Errors.push_back(CurrentFn->Name +
                   ": unsupported aggregate field base expression");
  return nullptr;
}

std::unique_ptr<VExpr> ASTConverter::convertExpr(const Expr *E) {
  if (!E)
    return nullptr;
  E = E->IgnoreParens();
  while (const auto *CE = dyn_cast<CastExpr>(E)) {
    if (CE->getCastKind() == CK_NoOp ||
        CE->getCastKind() == CK_LValueToRValue ||
        CE->getCastKind() == CK_ConstructorConversion)
      E = CE->getSubExpr()->IgnoreParens();
    else
      break;
  }

  if (const auto *MTE = dyn_cast<MaterializeTemporaryExpr>(E))
    return convertExpr(MTE->getSubExpr());
  if (isa<CXXNewExpr>(E)) {
    Errors.push_back(CurrentFn->Name +
                     ": new-expressions are only supported as direct local "
                     "pointer initializers");
    return nullptr;
  }
  if (isa<CXXDeleteExpr>(E)) {
    Errors.push_back(CurrentFn->Name +
                     ": delete-expressions are only supported as statements");
    return nullptr;
  }
  if (const auto *IL = dyn_cast<InitListExpr>(E)) {
    if (E->getType()->isRecordType()) {
      Errors.push_back(CurrentFn->Name +
                       ": aggregate initializer used as a scalar expression");
      return nullptr;
    }
    if (IL->getNumInits() == 1)
      return convertExpr(IL->getInit(0));
    if (IL->getNumInits() != 0) {
      Errors.push_back(CurrentFn->Name +
                       ": scalar initializer must contain at most one value");
      return nullptr;
    }
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    if (Ty.Kind == VTypeKind::Bool)
      return std::make_unique<VLiteralExpr>(false, Ty, E->getExprLoc());
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64 ||
        Ty.Kind == VTypeKind::Ptr)
      return std::make_unique<VLiteralExpr>(0, Ty, E->getExprLoc());
    Errors.push_back(CurrentFn->Name +
                     ": unsupported empty scalar initializer");
    return nullptr;
  }
  if (const auto *ValueInit = dyn_cast<CXXScalarValueInitExpr>(E)) {
    VType Ty = VType::fromQualType(ValueInit->getType(), IntMode, Ctx);
    if (Ty.Kind == VTypeKind::Bool)
      return std::make_unique<VLiteralExpr>(false, Ty, E->getExprLoc());
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64 ||
        Ty.Kind == VTypeKind::Ptr)
      return std::make_unique<VLiteralExpr>(0, Ty, E->getExprLoc());
    Errors.push_back(CurrentFn->Name +
                     ": unsupported scalar value initialization");
    return nullptr;
  }
  if (const auto *CE = dyn_cast<CXXConstructExpr>(E)) {
    if (CE->getNumArgs() == 1 && CE->getConstructor()->isTrivial())
      return convertExpr(CE->getArg(0));
    Errors.push_back(CurrentFn->Name + ": unsupported constructor expression");
    return nullptr;
  }
  if (const auto *IL = dyn_cast<IntegerLiteral>(E)) {
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    return std::make_unique<VLiteralExpr>(
        integerValueString(IL->getValue(), Ty.IsSigned), Ty, E->getExprLoc());
  }
  if (const auto *BL = dyn_cast<CXXBoolLiteralExpr>(E)) {
    return std::make_unique<VLiteralExpr>(BL->getValue(), VType::makeBool(),
                                          E->getExprLoc());
  }
  if (isa<CXXNullPtrLiteralExpr>(E)) {
    return std::make_unique<VLiteralExpr>(0, VType::makePtr(), E->getExprLoc());
  }
  if (isa<ImplicitValueInitExpr>(E)) {
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    if (Ty.Kind == VTypeKind::Bool)
      return std::make_unique<VLiteralExpr>(false, Ty, E->getExprLoc());
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64 ||
        Ty.Kind == VTypeKind::Ptr)
      return std::make_unique<VLiteralExpr>(0, Ty, E->getExprLoc());
    Errors.push_back(CurrentFn->Name +
                     ": unsupported implicit aggregate initialization");
    return nullptr;
  }
  if (const auto *Trait = dyn_cast<UnaryExprOrTypeTraitExpr>(E)) {
    QualType ArgumentType = Trait->getTypeOfArgument();
    if (const auto *Reference = ArgumentType->getAs<ReferenceType>())
      ArgumentType = Reference->getPointeeType();
    CharUnits Value;
    switch (Trait->getKind()) {
    case UETT_SizeOf:
      Value = Ctx.getTypeSizeInChars(ArgumentType);
      break;
    case UETT_AlignOf:
      Value = Ctx.getTypeAlignInChars(ArgumentType);
      break;
    default:
      Errors.push_back(CurrentFn->Name +
                       ": unsupported unary type trait expression");
      return nullptr;
    }
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    return std::make_unique<VLiteralExpr>(std::to_string(Value.getQuantity()),
                                          Ty, E->getExprLoc());
  }
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    if (const auto *FD = dyn_cast<FieldDecl>(DRE->getDecl())) {
      auto It = FieldSubstPrefix.find(FD->getNameAsString());
      if (It != FieldSubstPrefix.end()) {
        VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
        return std::make_unique<VVarExpr>(It->second + FD->getNameAsString(),
                                          Ty, E->getExprLoc());
      }
    }
    if (const auto *ECD = dyn_cast<EnumConstantDecl>(DRE->getDecl())) {
      VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
      return std::make_unique<VLiteralExpr>(
          integerValueString(ECD->getInitVal()), Ty, E->getExprLoc());
    }
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      auto Bound = BoundValues.find(VD);
      if (!VD->isLocalVarDeclOrParm() && Bound == BoundValues.end()) {
        Errors.push_back(CurrentFn->Name +
                         ": global variable access is unsupported: " +
                         VD->getNameAsString());
        return nullptr;
      }
      requireInitialized(VD);
      if (VD->getType()->isReferenceType()) {
        auto Address = convertLValueAddress(E);
        if (!Address) {
          Errors.push_back(CurrentFn->Name +
                           ": unsupported reference value expression");
          return nullptr;
        }
        VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
        return std::make_unique<VLoadExpr>(std::move(Address), Ty,
                                           E->getExprLoc());
      }
      VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
      std::string ProvenanceVariable;
      if (auto It = DynamicPointerProvenanceVariables.find(VD);
          It != DynamicPointerProvenanceVariables.end())
        ProvenanceVariable = It->second;
      return std::make_unique<VVarExpr>(
          Bound == BoundValues.end() ? valueName(VD) : Bound->second, Ty,
          E->getExprLoc(), std::move(ProvenanceVariable));
    }
  }
  if (const auto *U = dyn_cast<UnaryOperator>(E)) {
    if (U->getOpcode() == UO_Deref) {
      if (referencesDynamicPointer(U->getSubExpr()) &&
          !directDynamicPointer(U->getSubExpr())) {
        Errors.push_back(CurrentFn->Name +
                         ": dynamic-storage dereference requires its direct "
                         "allocation pointer");
        return nullptr;
      }
      auto Ptr = convertExpr(U->getSubExpr());
      if (!Ptr)
        return nullptr;
      VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
      return std::make_unique<VLoadExpr>(std::move(Ptr), Ty, E->getExprLoc());
    }
    auto Op = convertExpr(U->getSubExpr());
    if (!Op)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    if (U->getOpcode() == UO_Minus)
      return std::make_unique<VUnaryOpExpr>(VUnaryOp::Neg, std::move(Op), Ty,
                                            E->getExprLoc());
    if (U->getOpcode() == UO_LNot)
      return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(Op), Ty,
                                            E->getExprLoc());
    if (U->getOpcode() == UO_Not) {
      if (IntMode == VIntMode::Math) {
        Errors.push_back(CurrentFn->Name +
                         ": bitwise operators are unsupported in "
                         "mathematical spec functions");
        return nullptr;
      }
      return std::make_unique<VUnaryOpExpr>(VUnaryOp::BitNot, std::move(Op), Ty,
                                            E->getExprLoc());
    }
    Errors.push_back(CurrentFn->Name + ": unsupported unary operator");
    return nullptr;
  }
  if (const auto *AS = dyn_cast<ArraySubscriptExpr>(E)) {
    if (referencesDynamicPointer(AS)) {
      Errors.push_back(
          CurrentFn->Name +
          ": subscripting dynamic-storage pointers is unsupported");
      return nullptr;
    }
    auto Base = convertExpr(AS->getBase());
    auto Idx = convertExpr(AS->getIdx());
    if (!Base || !Idx)
      return nullptr;
    const uint64_t PointeeSize = Base->Ty.PointeeSizeBytes;
    Idx = scalePointerOffset(std::move(Idx), PointeeSize, E->getExprLoc());
    if (!Idx) {
      Errors.push_back(CurrentFn->Name +
                       ": pointer arithmetic requires a complete pointee type");
      return nullptr;
    }
    auto Addr = std::make_unique<VBinOpExpr>(
        VBinOp::Add, std::move(Base), std::move(Idx),
        VType::makePtr(PointeeSize), E->getExprLoc());
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    return std::make_unique<VLoadExpr>(std::move(Addr), Ty, E->getExprLoc());
  }
  if (const auto *B = dyn_cast<BinaryOperator>(E)) {
    std::optional<VBinOp> Op = convertBinOpcode(B->getOpcode());
    if (!Op) {
      Errors.push_back(CurrentFn->Name + ": unsupported binary operator");
      return nullptr;
    }
    if (IntMode == VIntMode::Math &&
        (*Op == VBinOp::BitAnd || *Op == VBinOp::BitOr ||
         *Op == VBinOp::BitXor || *Op == VBinOp::Shl || *Op == VBinOp::Shr)) {
      Errors.push_back(CurrentFn->Name +
                       ": bitwise operators are unsupported in mathematical "
                       "spec functions");
      return nullptr;
    }
    const bool LeftPointer = B->getLHS()->getType()->isPointerType();
    const bool RightPointer = B->getRHS()->getType()->isPointerType();
    if (B->getOpcode() == BO_Sub && LeftPointer && RightPointer) {
      if (CurrentFn->IsSpec) {
        Errors.push_back(
            CurrentFn->Name +
            ": pointer difference in spec or lifted constexpr functions is "
            "unsupported");
        return nullptr;
      }
      QualType LeftPointee =
          B->getLHS()->getType()->getPointeeType().getUnqualifiedType();
      QualType RightPointee =
          B->getRHS()->getType()->getPointeeType().getUnqualifiedType();
      if (!Ctx.hasSameType(LeftPointee, RightPointee) ||
          LeftPointee->isIncompleteType()) {
        Errors.push_back(CurrentFn->Name +
                         ": pointer difference requires matching complete "
                         "pointee types");
        return nullptr;
      }
      const uint64_t PointeeSize =
          Ctx.getTypeSizeInChars(LeftPointee).getQuantity();
      auto L = convertPointerDifferenceOperand(B->getLHS(), PointeeSize);
      auto R = convertPointerDifferenceOperand(B->getRHS(), PointeeSize);
      if (!L || !R) {
        Errors.push_back(
            CurrentFn->Name +
            ": pointer difference operands must be direct pointers or +0/+1 "
            "positions within one complete object");
        return nullptr;
      }
      VType AddressType = VType::makePtr(PointeeSize);
      auto ByteDifference =
          std::make_unique<VBinOpExpr>(VBinOp::Sub, std::move(L), std::move(R),
                                       AddressType, E->getExprLoc());
      auto Stride = std::make_unique<VLiteralExpr>(
          std::to_string(PointeeSize), AddressType, E->getExprLoc());
      auto ElementDifference = std::make_unique<VBinOpExpr>(
          VBinOp::Div, std::move(ByteDifference), std::move(Stride),
          AddressType, E->getExprLoc());
      VType ResultType = VType::fromQualType(E->getType(), IntMode, Ctx);
      return std::make_unique<VCastExpr>(std::move(ElementDifference),
                                         AddressType, ResultType,
                                         E->getExprLoc());
    }
    if ((B->getOpcode() == BO_Add || B->getOpcode() == BO_Sub) &&
        referencesDynamicPointer(B)) {
      Errors.push_back(CurrentFn->Name +
                       ": arithmetic on dynamic-storage pointers is "
                       "unsupported");
      return nullptr;
    }
    if ((B->getOpcode() == BO_LT || B->getOpcode() == BO_LE ||
         B->getOpcode() == BO_GT || B->getOpcode() == BO_GE) &&
        referencesDynamicPointer(B)) {
      Errors.push_back(CurrentFn->Name +
                       ": ordering dynamic-storage pointers is unsupported");
      return nullptr;
    }
    auto L = convertExpr(B->getLHS());
    auto R = convertExpr(B->getRHS());
    if (!L || !R)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    if (Ty.Kind == VTypeKind::Ptr &&
        (B->getOpcode() == BO_Add || B->getOpcode() == BO_Sub)) {
      if (!LeftPointer)
        L = scalePointerOffset(std::move(L), Ty.PointeeSizeBytes,
                               E->getExprLoc());
      else if (!RightPointer)
        R = scalePointerOffset(std::move(R), Ty.PointeeSizeBytes,
                               E->getExprLoc());
      if (!L || !R) {
        Errors.push_back(
            CurrentFn->Name +
            ": pointer arithmetic requires a complete pointee type");
        return nullptr;
      }
    }
    return std::make_unique<VBinOpExpr>(*Op, std::move(L), std::move(R), Ty,
                                        E->getExprLoc());
  }
  if (const auto *ICE = dyn_cast<ImplicitCastExpr>(E)) {
    if (ICE->getCastKind() == CK_NullToPointer)
      return std::make_unique<VLiteralExpr>(0, VType::makePtr(),
                                            E->getExprLoc());
    auto Inner = convertExpr(ICE->getSubExpr());
    if (!Inner)
      return nullptr;
    VType To = VType::fromQualType(E->getType(), IntMode, Ctx);
    VType From = Inner->Ty;
    auto IsIntegral = [](VTypeKind K) {
      return K == VTypeKind::Int32 || K == VTypeKind::Int64 ||
             K == VTypeKind::Bool;
    };
    const bool IntegralCast = IsIntegral(From.Kind) && IsIntegral(To.Kind);
    const bool PointerToBool =
        From.Kind == VTypeKind::Ptr && To.Kind == VTypeKind::Bool;
    if (!IntegralCast && !PointerToBool) {
      Errors.push_back(CurrentFn->Name +
                       ": unsupported implicit pointer or aggregate cast");
      return nullptr;
    }
    return std::make_unique<VCastExpr>(std::move(Inner), From, To,
                                       E->getExprLoc());
  }
  if (const auto *CE = dyn_cast<ExplicitCastExpr>(E)) {
    if (CE->getCastKind() == CK_NullToPointer)
      return std::make_unique<VLiteralExpr>(0, VType::makePtr(),
                                            E->getExprLoc());
    auto Inner = convertExpr(CE->getSubExpr());
    if (!Inner)
      return nullptr;
    VType To = VType::fromQualType(E->getType(), IntMode, Ctx);
    VType From = Inner->Ty;
    auto IsIntegral = [](VTypeKind K) {
      return K == VTypeKind::Int32 || K == VTypeKind::Int64 ||
             K == VTypeKind::Bool;
    };
    const bool IntegralCast = IsIntegral(From.Kind) && IsIntegral(To.Kind);
    const bool PointerToBool =
        From.Kind == VTypeKind::Ptr && To.Kind == VTypeKind::Bool;
    if (!IntegralCast && !PointerToBool) {
      Errors.push_back(CurrentFn->Name +
                       ": unsupported explicit pointer or aggregate cast");
      return nullptr;
    }
    return std::make_unique<VCastExpr>(std::move(Inner), From, To,
                                       E->getExprLoc());
  }
  if (const auto *O = dyn_cast<OldExpr>(E)) {
    bool Saved = InOld;
    InOld = true;
    auto Inner = convertExpr(O->getInner());
    InOld = Saved;
    if (!Inner)
      return nullptr;
    VType Ty = Inner->Ty;
    return std::make_unique<VOldExpr>(std::move(Inner), Ty, E->getExprLoc());
  }
  if (const auto *C = dyn_cast<ConditionalOperator>(E)) {
    auto Cond = convertExpr(C->getCond());
    auto T = convertExpr(C->getTrueExpr());
    auto F = convertExpr(C->getFalseExpr());
    if (!Cond || !T || !F)
      return nullptr;
    VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
    return std::make_unique<VConditionalExpr>(
        std::move(Cond), std::move(T), std::move(F), Ty, E->getExprLoc());
  }
  if (const auto *M = dyn_cast<MemberExpr>(E)) {
    if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
      const Expr *Base = M->getBase()->IgnoreParenImpCasts();
      if (isa<CXXThisExpr>(Base)) {
        auto It = FieldSubstPrefix.find(FD->getNameAsString());
        if (It != FieldSubstPrefix.end()) {
          VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
          return std::make_unique<VVarExpr>(It->second + FD->getNameAsString(),
                                            Ty, E->getExprLoc());
        }
      }
    }
    if (auto Address = convertArrowFieldAddress(M)) {
      VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
      return std::make_unique<VLoadExpr>(std::move(Address), Ty,
                                         E->getExprLoc());
    }
    if (const auto *DRE =
            dyn_cast<DeclRefExpr>(M->getBase()->IgnoreParenImpCasts())) {
      if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
        if (!VD->isLocalVarDeclOrParm()) {
          Errors.push_back(CurrentFn->Name +
                           ": global aggregate access is unsupported");
          return nullptr;
        }
        if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
          requireInitialized(VD, FD);
          VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
          std::string Name = valueName(VD) + "." + FD->getNameAsString();
          return std::make_unique<VVarExpr>(Name, Ty, E->getExprLoc());
        }
      }
      if (const auto *PD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
        if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
          VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
          std::string Name = valueName(PD) + "." + FD->getNameAsString();
          return std::make_unique<VVarExpr>(Name, Ty, E->getExprLoc());
        }
      }
    }
    if (InPost && isa<ResultExpr>(M->getBase()->IgnoreParenImpCasts())) {
      if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl())) {
        VType Ty = VType::fromQualType(E->getType(), IntMode, Ctx);
        return std::make_unique<VVarExpr>("result." + FD->getNameAsString(), Ty,
                                          E->getExprLoc());
      }
    }
    auto Base = convertExpr(M->getBase());
    if (!Base)
      return nullptr;
    if (const auto *FD = dyn_cast<FieldDecl>(M->getMemberDecl()))
      return convertRecordField(std::move(Base), FD, E->getExprLoc());
  }
  if (dyn_cast<ResultExpr>(E)) {
    if (!InPost) {
      Errors.push_back(CurrentFn->Name +
                       ": result expression outside a postcondition");
      return nullptr;
    }
    if (InOld) {
      Errors.push_back(CurrentFn->Name +
                       ": result has no value in the function pre-state");
      return nullptr;
    }
    return std::make_unique<VResultExpr>(
        VType::fromQualType(E->getType(), IntMode, Ctx), E->getExprLoc());
  }
  if (const auto *F = dyn_cast<ForallExpr>(E)) {
    std::string Binder =
        "__cppverify_bound_" + std::to_string(BoundValueId++) + "_" +
        (F->getBoundVar() ? F->getBoundVar()->getNameAsString() : "i");
    auto Lo = convertExpr(F->getLo());
    auto Hi = convertExpr(F->getHi());
    if (F->getBoundVar())
      BoundValues.emplace(F->getBoundVar(), Binder);
    auto Body = convertExpr(F->getBody());
    if (F->getBoundVar())
      BoundValues.erase(F->getBoundVar());
    if (!Lo || !Hi || !Body)
      return nullptr;
    VType BinderType =
        F->getBoundVar()
            ? VType::fromQualType(F->getBoundVar()->getType(), IntMode, Ctx)
            : VType::makeInt32(IntMode);
    return std::make_unique<VForallExpr>(Binder, std::move(Lo), std::move(Hi),
                                         std::move(Body), E->getExprLoc(),
                                         BinderType);
  }
  if (const auto *Ex = dyn_cast<ExistsExpr>(E)) {
    std::string Binder =
        "__cppverify_bound_" + std::to_string(BoundValueId++) + "_" +
        (Ex->getBoundVar() ? Ex->getBoundVar()->getNameAsString() : "i");
    auto Lo = convertExpr(Ex->getLo());
    auto Hi = convertExpr(Ex->getHi());
    if (Ex->getBoundVar())
      BoundValues.emplace(Ex->getBoundVar(), Binder);
    auto Body = convertExpr(Ex->getBody());
    if (Ex->getBoundVar())
      BoundValues.erase(Ex->getBoundVar());
    if (!Lo || !Hi || !Body)
      return nullptr;
    VType BinderType =
        Ex->getBoundVar()
            ? VType::fromQualType(Ex->getBoundVar()->getType(), IntMode, Ctx)
            : VType::makeInt32(IntMode);
    return std::make_unique<VExistsExpr>(Binder, std::move(Lo), std::move(Hi),
                                         std::move(Body), E->getExprLoc(),
                                         BinderType);
  }
  if (const auto *CE = dyn_cast<CallExpr>(E)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if (Callee->isConstexpr() && !functionContract(Callee) &&
          CE->isEvaluatable(Ctx)) {
        Expr::EvalResult EV;
        if (CE->EvaluateAsInt(EV, Ctx)) {
          VType Ty = VType::fromQualType(E->getType(), VIntMode::Machine, Ctx);
          return std::make_unique<VLiteralExpr>(
              integerValueString(EV.Val.getInt()), Ty, E->getExprLoc());
        }
      }
      if (calleeIsSpec(Callee)) {
        for (const Expr *A : CE->arguments())
          if (referencesDynamicPointer(A)) {
            Errors.push_back(
                CurrentFn->Name +
                ": dynamic-storage pointers cannot cross a function-call "
                "boundary");
            return nullptr;
          }
        std::vector<std::unique_ptr<VExpr>> Args;
        unsigned ArgIndex = 0;
        for (const Expr *A : CE->arguments()) {
          const ParmVarDecl *Formal = ArgIndex < Callee->getNumParams()
                                          ? Callee->getParamDecl(ArgIndex)
                                          : nullptr;
          if (Formal && Formal->getType()->isRecordType()) {
            appendRecordCallArgument(A, Formal, Args);
          } else if (auto AE = convertExpr(A)) {
            Args.push_back(std::move(AE));
          }
          ++ArgIndex;
        }
        VType Ty = VType::fromQualType(
            E->getType(),
            InContractExpression ? specCallIntMode(Callee) : IntMode, Ctx);
        return std::make_unique<VSpecCallExpr>(
            Callee->getNameAsString(), functionIdentity(Callee),
            std::move(Args), Ty, E->getExprLoc());
      }
      if (functionContract(Callee))
        Errors.push_back(CurrentFn->Name +
                         ": executable call is unsupported in this expression "
                         "context: " +
                         Callee->getNameAsString());
      else
        Errors.push_back(
            CurrentFn->Name +
            ": call to function without a verification contract: " +
            Callee->getNameAsString());
    }
  }
  Errors.push_back(CurrentFn->Name +
                   ": unsupported expression: " + E->getStmtClassName());
  return nullptr;
}

void ASTConverter::convertExecCallArg(
    const Expr *E, const ParmVarDecl *Formal,
    std::vector<std::unique_ptr<VStmt>> &Prelude, std::unique_ptr<VExpr> &Out) {
  if (!E) {
    Out = nullptr;
    return;
  }
  if (Formal && Formal->getType()->isReferenceType()) {
    if (!Formal->getType()->isLValueReferenceType()) {
      Errors.push_back(CurrentFn->Name +
                       ": rvalue-reference arguments are unsupported");
      Out = nullptr;
      return;
    }
    const size_t ErrorCount = Errors.size();
    Out = convertLValueAddress(E);
    if (!Out && Errors.size() == ErrorCount)
      Errors.push_back(
          CurrentFn->Name +
          ": reference arguments require another reference parameter or a "
          "direct pointer dereference");
    return;
  }
  const VarDecl *Source = directDynamicPointer(E);
  if (Source ||
      (referencesDynamicPointer(E) && E->getType()->isPointerType())) {
    if (!Source || !Formal || !Formal->getType()->isPointerType() ||
        !Ctx.hasSameUnqualifiedType(Formal->getType()->getPointeeType(),
                                    Source->getType()->getPointeeType())) {
      Errors.push_back(
          CurrentFn->Name +
          ": dynamic-storage pointer arguments require matching direct pointer "
          "parameters");
      Out = nullptr;
      return;
    }
  }
  const Expr *CallExprCandidate = E->IgnoreParenImpCasts();
  if (const auto *CE = dyn_cast<CallExpr>(CallExprCandidate)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if (functionContract(Callee) && !calleeIsSpec(Callee) &&
          !calleeIsProof(Callee)) {
        std::vector<std::unique_ptr<VExpr>> InnerArgs;
        convertExecCallArgs(CE, Prelude, InnerArgs);
        std::string Tmp = "__nested_" + std::to_string(++NestedCallId);
        Prelude.push_back(std::make_unique<VCallStmt>(
            Callee->getNameAsString(), functionIdentity(Callee),
            std::move(InnerArgs), Tmp, E->getExprLoc(), false));
        Out = convertCallResultValue(
            Tmp, Callee->getReturnType(),
            VType::fromQualType(E->getType(), IntMode, Ctx), E->getExprLoc());
        return;
      }
    }
  }
  Out = convertExpr(E);
}

std::unique_ptr<VExpr> ASTConverter::convertCallResultValue(
    std::string Name, QualType SourceType, const VType &TargetType,
    SourceLocation Loc, std::string Provenance) {
  VType Source = VType::fromQualType(SourceType, IntMode, Ctx);
  if (TargetType.Kind == VTypeKind::Void)
    return nullptr;
  auto Value = std::make_unique<VVarExpr>(
      std::move(Name), Source, Loc,
      Source.Kind == VTypeKind::Ptr ? std::move(Provenance) : std::string());
  auto SameType = [](const VType &L, const VType &R) {
    return L.Kind == R.Kind && L.IntMode == R.IntMode &&
           L.IsSigned == R.IsSigned && L.BitWidth == R.BitWidth;
  };
  if (SameType(Source, TargetType) ||
      (Source.Kind == VTypeKind::Ptr && TargetType.Kind == VTypeKind::Ptr) ||
      (Source.Kind == VTypeKind::Struct &&
       TargetType.Kind == VTypeKind::Struct))
    return Value;
  auto IsIntegral = [](VTypeKind K) {
    return K == VTypeKind::Int32 || K == VTypeKind::Int64 ||
           K == VTypeKind::Bool;
  };
  if ((IsIntegral(Source.Kind) && IsIntegral(TargetType.Kind)) ||
      (Source.Kind == VTypeKind::Ptr && TargetType.Kind == VTypeKind::Bool))
    return std::make_unique<VCastExpr>(std::move(Value), Source, TargetType,
                                       Loc);
  Errors.push_back(CurrentFn->Name +
                   ": unsupported executable call result conversion");
  return nullptr;
}

void ASTConverter::convertExecCallArgs(
    const CallExpr *CE, std::vector<std::unique_ptr<VStmt>> &Prelude,
    std::vector<std::unique_ptr<VExpr>> &Args) {
  if (!CE)
    return;
  const FunctionDecl *Callee = CE->getDirectCallee();

  if ((InGhost || CurrentFn->IsProof) && Callee && !calleeIsProof(Callee)) {
    Errors.push_back(CurrentFn->Name +
                     ": proof-only code cannot call executable functions");
    return;
  }

  auto IsModifyingCall = [&](const Expr *E) {
    const auto *Nested = dyn_cast<CallExpr>(E->IgnoreParenImpCasts());
    const FunctionDecl *NestedCallee =
        Nested ? Nested->getDirectCallee() : nullptr;
    const FunctionContractInfo *FCI =
        NestedCallee ? functionContract(NestedCallee) : nullptr;
    if (!FCI || calleeIsSpec(NestedCallee) || calleeIsProof(NestedCallee))
      return false;
    if (!FCI->Modifies.empty())
      return true;
    for (const ParmVarDecl *Param : NestedCallee->parameters())
      if (Param->getType()->isPointerType() ||
          Param->getType()->isReferenceType())
        return true;
    return false;
  };
  std::function<bool(const Stmt *)> IsHeapSensitive = [&](const Stmt *S) {
    if (!S)
      return false;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(S))
      if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
        if (VD->getType()->isReferenceType())
          return true;
    if (const auto *U = dyn_cast<UnaryOperator>(S))
      if (U->getOpcode() == UO_Deref)
        return true;
    if (const auto *M = dyn_cast<MemberExpr>(S))
      if (M->isArrow())
        return true;
    if (isa<ArraySubscriptExpr>(S))
      return true;
    if (const auto *Nested = dyn_cast<CallExpr>(S)) {
      const FunctionDecl *NestedCallee = Nested->getDirectCallee();
      if (NestedCallee && functionContract(NestedCallee) &&
          !calleeIsSpec(NestedCallee) && !calleeIsProof(NestedCallee))
        return true;
    }
    for (const Stmt *Child : S->children())
      if (IsHeapSensitive(Child))
        return true;
    return false;
  };

  for (unsigned I = 0; I < CE->getNumArgs(); ++I) {
    if (!IsModifyingCall(CE->getArg(I)))
      continue;
    for (unsigned J = 0; J < CE->getNumArgs(); ++J) {
      if (I != J && IsHeapSensitive(CE->getArg(J))) {
        Errors.push_back(
            CurrentFn->Name +
            ": call arguments have order-dependent heap evaluations");
        return;
      }
    }
  }

  unsigned ArgIndex = 0;
  for (const Expr *A : CE->arguments()) {
    const ParmVarDecl *Formal = Callee && ArgIndex < Callee->getNumParams()
                                    ? Callee->getParamDecl(ArgIndex)
                                    : nullptr;
    if (Formal && Formal->getType()->isRecordType()) {
      appendRecordCallArgument(A, Formal, Args);
    } else {
      std::unique_ptr<VExpr> Arg;
      convertExecCallArg(A, Formal, Prelude, Arg);
      if (Arg)
        Args.push_back(std::move(Arg));
    }
    ++ArgIndex;
  }
}

bool ASTConverter::appendRecordCallArgument(
    const Expr *E, const ParmVarDecl *Formal,
    std::vector<std::unique_ptr<VExpr>> &Args) {
  auto Base = convertExpr(E);
  if (!Base)
    return false;
  const RecordDecl *RD = getRecordFromType(Formal->getType());
  const RecordDecl *Definition = RD ? RD->getDefinition() : nullptr;
  if (!Definition)
    return false;
  for (const FieldDecl *Field : Definition->fields()) {
    auto FieldValue =
        convertRecordField(cloneVExpr(Base.get()), Field, E->getExprLoc());
    if (!FieldValue)
      return false;
    Args.push_back(std::move(FieldValue));
  }
  return true;
}

std::unique_ptr<VExpr>
ASTConverter::convertAssignmentValue(const BinaryOperator *Assignment) {
  if (Assignment->getOpcode() != BO_Assign &&
      Assignment->getLHS()->getType()->isPointerType()) {
    Errors.push_back(CurrentFn->Name +
                     ": pointer compound assignment is unsupported");
    return nullptr;
  }
  auto RHS = convertExpr(Assignment->getRHS());
  if (!RHS)
    return nullptr;
  if (Assignment->getOpcode() == BO_Assign)
    return RHS;

  VBinOp Op;
  switch (Assignment->getOpcode()) {
  case BO_AddAssign:
    Op = VBinOp::Add;
    break;
  case BO_SubAssign:
    Op = VBinOp::Sub;
    break;
  case BO_MulAssign:
    Op = VBinOp::Mul;
    break;
  case BO_DivAssign:
    Op = VBinOp::Div;
    break;
  case BO_RemAssign:
    Op = VBinOp::Rem;
    break;
  case BO_AndAssign:
    Op = VBinOp::BitAnd;
    break;
  case BO_OrAssign:
    Op = VBinOp::BitOr;
    break;
  case BO_XorAssign:
    Op = VBinOp::BitXor;
    break;
  case BO_ShlAssign:
    Op = VBinOp::Shl;
    break;
  case BO_ShrAssign:
    Op = VBinOp::Shr;
    break;
  default:
    Errors.push_back(CurrentFn->Name +
                     ": unsupported compound assignment operator");
    return nullptr;
  }

  auto LHS = convertExpr(Assignment->getLHS());
  if (!LHS)
    return nullptr;
  const auto *Compound = cast<CompoundAssignOperator>(Assignment);
  VType TargetTy =
      VType::fromQualType(Assignment->getLHS()->getType(), IntMode, Ctx);
  VType LHSComputationTy =
      VType::fromQualType(Compound->getComputationLHSType(), IntMode, Ctx);
  VType ResultTy =
      VType::fromQualType(Compound->getComputationResultType(), IntMode, Ctx);
  auto SameType = [](const VType &A, const VType &B) {
    return A.Kind == B.Kind && A.IntMode == B.IntMode &&
           A.IsSigned == B.IsSigned && A.BitWidth == B.BitWidth;
  };
  if (!SameType(LHS->Ty, LHSComputationTy)) {
    VType LHSSourceTy = LHS->Ty;
    LHS =
        std::make_unique<VCastExpr>(std::move(LHS), LHSSourceTy,
                                    LHSComputationTy, Assignment->getExprLoc());
  }
  std::unique_ptr<VExpr> Value = std::make_unique<VBinOpExpr>(
      Op, std::move(LHS), std::move(RHS), ResultTy, Assignment->getExprLoc());
  if (!SameType(ResultTy, TargetTy))
    return std::make_unique<VCastExpr>(std::move(Value), ResultTy, TargetTy,
                                       Assignment->getExprLoc());
  return Value;
}

void ASTConverter::appendAssignment(const Expr *LHS,
                                    std::unique_ptr<VExpr> Value,
                                    SourceLocation Loc,
                                    std::vector<std::unique_ptr<VStmt>> &Out) {
  if (!LHS || !Value)
    return;
  if (!ghostAssignmentAllowed(LHS)) {
    Errors.push_back(CurrentFn->Name +
                     ": ghost code cannot modify executable state");
    return;
  }
  LHS = LHS->IgnoreParenImpCasts();

  if (const auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
    if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
      if (!VD->isLocalVarDeclOrParm()) {
        Errors.push_back(CurrentFn->Name +
                         ": global variable assignment is unsupported: " +
                         VD->getNameAsString());
        return;
      }
      if (VD->getType()->isReferenceType()) {
        if (VD->getType().getNonReferenceType().isConstQualified()) {
          Errors.push_back(CurrentFn->Name +
                           ": assignment through a const reference is "
                           "unsupported");
          return;
        }
        if (CurrentFn->IsProof) {
          Errors.push_back(CurrentFn->Name +
                           ": proof functions cannot modify executable memory");
          return;
        }
        auto Address = convertLValueAddress(LHS);
        if (!Address) {
          Errors.push_back(CurrentFn->Name +
                           ": unsupported reference assignment target");
          return;
        }
        Out.push_back(std::make_unique<VStoreStmt>(std::move(Address),
                                                   std::move(Value), Loc));
        return;
      }
      if (VD->getType()->isRecordType()) {
        Errors.push_back(CurrentFn->Name +
                         ": aggregate assignment is unsupported");
        return;
      }
      Out.push_back(
          std::make_unique<VAssignStmt>(valueName(VD), std::move(Value), Loc));
      markInitialized(VD);
      return;
    }
  }

  if (const auto *ME = dyn_cast<MemberExpr>(LHS)) {
    if (auto Address = convertArrowFieldAddress(ME)) {
      if (CurrentFn->IsProof) {
        Errors.push_back(CurrentFn->Name +
                         ": proof functions cannot modify executable memory");
        return;
      }
      Out.push_back(std::make_unique<VStoreStmt>(std::move(Address),
                                                 std::move(Value), Loc));
      return;
    }
    const auto *FD = dyn_cast<FieldDecl>(ME->getMemberDecl());
    const auto *DRE =
        dyn_cast<DeclRefExpr>(ME->getBase()->IgnoreParenImpCasts());
    const auto *VD = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
    if (FD && VD) {
      if (!VD->isLocalVarDeclOrParm()) {
        Errors.push_back(CurrentFn->Name +
                         ": global aggregate assignment is unsupported");
        return;
      }
      Out.push_back(std::make_unique<VAssignStmt>(
          valueName(VD) + "." + FD->getNameAsString(), std::move(Value), Loc));
      markInitialized(VD, FD);
      return;
    }
  }

  if (const auto *U = dyn_cast<UnaryOperator>(LHS)) {
    if (U->getOpcode() == UO_Deref) {
      if (CurrentFn->IsProof) {
        Errors.push_back(CurrentFn->Name +
                         ": proof functions cannot modify executable memory");
        return;
      }
      if (referencesDynamicPointer(U->getSubExpr()) &&
          !directDynamicPointer(U->getSubExpr())) {
        Errors.push_back(CurrentFn->Name +
                         ": dynamic-storage dereference requires its direct "
                         "allocation pointer");
        return;
      }
      auto Ptr = convertExpr(U->getSubExpr());
      if (Ptr) {
        Out.push_back(std::make_unique<VStoreStmt>(std::move(Ptr),
                                                   std::move(Value), Loc));
        return;
      }
    }
  }

  if (const auto *AS = dyn_cast<ArraySubscriptExpr>(LHS)) {
    if (CurrentFn->IsProof) {
      Errors.push_back(CurrentFn->Name +
                       ": proof functions cannot modify executable memory");
      return;
    }
    if (referencesDynamicPointer(AS)) {
      Errors.push_back(
          CurrentFn->Name +
          ": subscripting dynamic-storage pointers is unsupported");
      return;
    }
    auto Base = convertExpr(AS->getBase());
    auto Index = convertExpr(AS->getIdx());
    if (Base && Index) {
      const uint64_t PointeeSize = Base->Ty.PointeeSizeBytes;
      Index = scalePointerOffset(std::move(Index), PointeeSize, Loc);
      if (!Index) {
        Errors.push_back(
            CurrentFn->Name +
            ": pointer arithmetic requires a complete pointee type");
        return;
      }
      auto Address = std::make_unique<VBinOpExpr>(
          VBinOp::Add, std::move(Base), std::move(Index),
          VType::makePtr(PointeeSize), Loc);
      Out.push_back(std::make_unique<VStoreStmt>(std::move(Address),
                                                 std::move(Value), Loc));
      return;
    }
  }

  Errors.push_back(CurrentFn->Name + ": unsupported assignment target");
}

bool ASTConverter::appendRecordCopy(const Expr *Source, const VarDecl *Target,
                                    SourceLocation Loc,
                                    std::vector<std::unique_ptr<VStmt>> &Out) {
  if (!Source || !Target)
    return false;
  Source = Source->IgnoreParenImpCasts();
  if (const auto *Construct = dyn_cast<CXXConstructExpr>(Source)) {
    if (Construct->getNumArgs() != 1 ||
        (!Construct->getConstructor()->isCopyConstructor() &&
         !Construct->getConstructor()->isMoveConstructor()))
      return false;
    Source = Construct->getArg(0)->IgnoreParenImpCasts();
  }
  const auto *DRE = dyn_cast<DeclRefExpr>(Source);
  const auto *SourceVar = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
  const RecordDecl *TargetRecord = getRecordFromType(Target->getType());
  const RecordDecl *SourceRecord =
      SourceVar ? getRecordFromType(SourceVar->getType()) : nullptr;
  if (!SourceVar || !Target->isLocalVarDeclOrParm() ||
      !SourceVar->isLocalVarDeclOrParm() || !TargetRecord || !SourceRecord ||
      !Ctx.hasSameUnqualifiedType(Target->getType(), SourceVar->getType()))
    return false;
  const RecordDecl *Definition = TargetRecord->getDefinition();
  if (!Definition)
    return false;
  for (const FieldDecl *Field : Definition->fields()) {
    requireInitialized(SourceVar, Field);
    VType Ty = VType::fromQualType(Field->getType(), IntMode, Ctx);
    auto Value = std::make_unique<VVarExpr>(
        valueName(SourceVar) + "." + Field->getNameAsString(), Ty, Loc);
    Out.push_back(std::make_unique<VAssignStmt>(valueName(Target) + "." +
                                                    Field->getNameAsString(),
                                                std::move(Value), Loc));
    markInitialized(Target, Field);
  }
  return true;
}

bool ASTConverter::appendRecordInitializer(
    const InitListExpr *Init, const VarDecl *Target, SourceLocation Loc,
    std::vector<std::unique_ptr<VStmt>> &Out) {
  if (!Init || !Target)
    return false;
  const RecordDecl *Record = getRecordFromType(Target->getType());
  const RecordDecl *Definition = Record ? Record->getDefinition() : nullptr;
  if (!Definition)
    return false;
  unsigned FieldCount = 0;
  for (const FieldDecl *Field : Definition->fields())
    (void)Field, ++FieldCount;
  if (Init->getNumInits() != FieldCount)
    return false;
  unsigned Index = 0;
  for (const FieldDecl *Field : Definition->fields()) {
    auto Value = convertExpr(Init->getInit(Index++));
    if (!Value)
      return true;
    Out.push_back(std::make_unique<VAssignStmt>(valueName(Target) + "." +
                                                    Field->getNameAsString(),
                                                std::move(Value), Loc));
    markInitialized(Target, Field);
  }
  return true;
}

std::vector<std::unique_ptr<VStmt>> ASTConverter::convertStmt(const Stmt *S) {
  std::vector<std::unique_ptr<VStmt>> Out;
  if (!S)
    return Out;
  if (isa<NullStmt>(S))
    return Out;

  if (const auto *CS = dyn_cast<CompoundStmt>(S)) {
    for (const Stmt *Child : CS->body()) {
      auto Part = convertStmt(Child);
      Out.insert(Out.end(), std::make_move_iterator(Part.begin()),
                 std::make_move_iterator(Part.end()));
    }
    return Out;
  }
  if (S->getStmtClass() == Stmt::ReturnStmtClass) {
    if (InGhost) {
      Errors.push_back(CurrentFn->Name +
                       ": ghost code cannot alter executable control flow");
      return Out;
    }
    const auto *RS = cast<ReturnStmt>(S);
    if (const Expr *RetE = RS->getRetValue()) {
      if (RetE->getType()->isPointerType() && referencesDynamicPointer(RetE)) {
        Errors.push_back(CurrentFn->Name +
                         ": dynamic-storage pointers cannot escape through a "
                         "return");
        return Out;
      }
      emitReturnInvariantAssert(RetE, Out, RS->getBeginLoc());
      const auto *CE = dyn_cast<CallExpr>(RetE->IgnoreParenImpCasts());
      if (CE) {
        if (const FunctionDecl *Callee = CE->getDirectCallee()) {
          if (functionContract(Callee) && !calleeIsSpec(Callee) &&
              !calleeIsProof(Callee)) {
            std::vector<std::unique_ptr<VExpr>> Args;
            convertExecCallArgs(CE, Out, Args);
            const std::string Tmp =
                "__return_call_" + std::to_string(++NestedCallId);
            const bool ReturnsVoid = Callee->getReturnType()->isVoidType();
            Out.push_back(std::make_unique<VCallStmt>(
                Callee->getNameAsString(), functionIdentity(Callee),
                std::move(Args), ReturnsVoid ? "" : Tmp, RS->getBeginLoc(),
                false));
            auto Result = convertCallResultValue(Tmp, Callee->getReturnType(),
                                                 CurrentFn->ReturnType,
                                                 RS->getBeginLoc());
            Out.push_back(std::make_unique<VReturnStmt>(std::move(Result),
                                                        RS->getBeginLoc()));
            InitializationPathReachable = false;
            return Out;
          }
        }
      }
      if (CurrentFn->ReturnType.Kind == VTypeKind::Struct) {
        auto RecordValue = convertExpr(RetE);
        if (!RecordValue)
          return Out;
        if (RecordValue->K == VExpr::Var) {
          Out.push_back(std::make_unique<VReturnStmt>(std::move(RecordValue),
                                                      RS->getBeginLoc()));
          InitializationPathReachable = false;
          return Out;
        }
        const RecordDecl *Record = getRecordFromType(RetE->getType());
        const RecordDecl *Definition =
            Record ? Record->getDefinition() : nullptr;
        if (!Definition) {
          Errors.push_back(CurrentFn->Name +
                           ": unsupported aggregate return expression");
          return Out;
        }
        const std::string Tmp =
            "__aggregate_return_" + std::to_string(++NestedCallId);
        for (const FieldDecl *Field : Definition->fields()) {
          auto FieldValue = convertRecordField(cloneVExpr(RecordValue.get()),
                                               Field, RS->getBeginLoc());
          if (!FieldValue)
            return Out;
          Out.push_back(std::make_unique<VAssignStmt>(
              Tmp + "." + Field->getNameAsString(), std::move(FieldValue),
              RS->getBeginLoc()));
        }
        Out.push_back(std::make_unique<VReturnStmt>(
            std::make_unique<VVarExpr>(Tmp, CurrentFn->ReturnType,
                                       RS->getBeginLoc()),
            RS->getBeginLoc()));
        InitializationPathReachable = false;
        return Out;
      }
    }
    std::unique_ptr<VExpr> Val;
    if (RS->getRetValue())
      Val = convertExpr(RS->getRetValue());
    Out.push_back(
        std::make_unique<VReturnStmt>(std::move(Val), RS->getBeginLoc()));
    InitializationPathReachable = false;
    return Out;
  }
  if (const auto *IS = dyn_cast<IfStmt>(S)) {
    if (IS->getInit()) {
      auto Init = convertStmt(IS->getInit());
      Out.insert(Out.end(), std::make_move_iterator(Init.begin()),
                 std::make_move_iterator(Init.end()));
    }
    if (IS->getConditionVariable()) {
      auto Init = convertStmt(IS->getConditionVariableDeclStmt());
      Out.insert(Out.end(), std::make_move_iterator(Init.begin()),
                 std::make_move_iterator(Init.end()));
    }
    auto Cond = convertExpr(IS->getCond());
    if (!Cond)
      return Out;
    const std::set<std::string> Before = InitializedValues;
    const bool BeforeReachable = InitializationPathReachable;
    auto Then = convertStmt(IS->getThen());
    const std::set<std::string> ThenInitialized = InitializedValues;
    const bool ThenReachable = InitializationPathReachable;
    InitializedValues = Before;
    InitializationPathReachable = BeforeReachable;
    std::vector<std::unique_ptr<VStmt>> Else;
    if (IS->getElse())
      Else = convertStmt(IS->getElse());
    const std::set<std::string> ElseInitialized = InitializedValues;
    const bool ElseReachable = InitializationPathReachable;
    if (ThenReachable && ElseReachable) {
      std::set<std::string> Merged;
      std::set_intersection(ThenInitialized.begin(), ThenInitialized.end(),
                            ElseInitialized.begin(), ElseInitialized.end(),
                            std::inserter(Merged, Merged.end()));
      InitializedValues = std::move(Merged);
    } else if (ThenReachable) {
      InitializedValues = ThenInitialized;
    } else if (ElseReachable) {
      InitializedValues = ElseInitialized;
    } else {
      InitializedValues = Before;
    }
    InitializationPathReachable = ThenReachable || ElseReachable;
    Out.push_back(std::make_unique<VIfStmt>(
        std::move(Cond), std::move(Then), std::move(Else), IS->getBeginLoc()));
    return Out;
  }
  if (const auto *WS = dyn_cast<WhileStmt>(S)) {
    if (WS->getConditionVariable()) {
      Errors.push_back(CurrentFn->Name +
                       ": while condition declarations are unsupported");
      return Out;
    }
    auto Cond = convertExpr(WS->getCond());
    if (!Cond)
      return Out;
    std::vector<std::unique_ptr<VExpr>> Invariants;
    std::vector<std::unique_ptr<VExpr>> Decreases;
    if (const LoopContractInfo *LCI = Ctx.getLoopContract(WS)) {
      bool SavedContract = InContractExpression;
      InContractExpression = true;
      for (const Expr *Inv : LCI->Invariants)
        if (auto E = convertExpr(Inv))
          Invariants.push_back(std::move(E));
      for (const Expr *D : LCI->Decreases)
        if (auto E = convertExpr(D))
          Decreases.push_back(std::move(E));
      InContractExpression = SavedContract;
    }
    if ((InGhost || CurrentFn->IsProof) && Decreases.empty()) {
      Errors.push_back(CurrentFn->Name +
                       ": proof-only loops require a decreases clause");
      return Out;
    }
    const std::set<std::string> Before = InitializedValues;
    const bool BeforeReachable = InitializationPathReachable;
    ++LoopDepth;
    auto Body = convertStmt(WS->getBody());
    --LoopDepth;
    InitializedValues = Before;
    InitializationPathReachable = BeforeReachable;
    Out.push_back(std::make_unique<VWhileStmt>(
        std::move(Cond), std::move(Invariants), std::move(Decreases),
        std::move(Body), WS->getBeginLoc()));
    return Out;
  }
  if (const auto *FS = dyn_cast<ForStmt>(S)) {
    if (FS->getConditionVariable()) {
      Errors.push_back(CurrentFn->Name +
                       ": for condition declarations are unsupported");
      return Out;
    }
    if (FS->getInit()) {
      auto Init = convertStmt(FS->getInit());
      Out.insert(Out.end(), std::make_move_iterator(Init.begin()),
                 std::make_move_iterator(Init.end()));
    }
    if (!FS->getCond()) {
      Errors.push_back(CurrentFn->Name +
                       ": conditionless for loops are unsupported");
      return Out;
    }
    auto Cond = convertExpr(FS->getCond());
    if (!Cond)
      return Out;
    std::vector<std::unique_ptr<VExpr>> Invariants;
    std::vector<std::unique_ptr<VExpr>> Decreases;
    if (const LoopContractInfo *LCI = Ctx.getLoopContract(FS)) {
      bool SavedContract = InContractExpression;
      InContractExpression = true;
      for (const Expr *Inv : LCI->Invariants)
        if (auto E = convertExpr(Inv))
          Invariants.push_back(std::move(E));
      for (const Expr *D : LCI->Decreases)
        if (auto E = convertExpr(D))
          Decreases.push_back(std::move(E));
      InContractExpression = SavedContract;
    }
    if ((InGhost || CurrentFn->IsProof) && Decreases.empty()) {
      Errors.push_back(CurrentFn->Name +
                       ": proof-only loops require a decreases clause");
      return Out;
    }
    const std::set<std::string> BeforeLoop = InitializedValues;
    const bool BeforeLoopReachable = InitializationPathReachable;
    ++LoopDepth;
    auto Body = convertStmt(FS->getBody());
    if (const Expr *Inc = FS->getInc()) {
      if (const auto *IncStmt = dyn_cast<Stmt>(Inc)) {
        auto IncPart = convertStmt(IncStmt);
        Body.insert(Body.end(), std::make_move_iterator(IncPart.begin()),
                    std::make_move_iterator(IncPart.end()));
      }
    }
    --LoopDepth;
    InitializedValues = BeforeLoop;
    InitializationPathReachable = BeforeLoopReachable;
    Out.push_back(std::make_unique<VWhileStmt>(
        std::move(Cond), std::move(Invariants), std::move(Decreases),
        std::move(Body), FS->getBeginLoc()));
    return Out;
  }
  if (const auto *OperatorCall = dyn_cast<CXXOperatorCallExpr>(S)) {
    if (OperatorCall->getOperator() == OO_Equal &&
        OperatorCall->getNumArgs() == 2 &&
        OperatorCall->getArg(0)->getType()->isRecordType()) {
      const auto *Assignment =
          dyn_cast_or_null<CXXMethodDecl>(OperatorCall->getDirectCallee());
      if (!Assignment ||
          (!Assignment->isCopyAssignmentOperator() &&
           !Assignment->isMoveAssignmentOperator()) ||
          !Assignment->isTrivial()) {
        Errors.push_back(CurrentFn->Name +
                         ": user-defined aggregate assignment is unsupported");
        return Out;
      }
      if (!ghostAssignmentAllowed(OperatorCall->getArg(0))) {
        Errors.push_back(CurrentFn->Name +
                         ": ghost code cannot modify executable state");
        return Out;
      }
      const Expr *TargetExpr = OperatorCall->getArg(0)->IgnoreParenImpCasts();
      const auto *DRE = dyn_cast<DeclRefExpr>(TargetExpr);
      const auto *Target = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
      if (Target && appendRecordCopy(OperatorCall->getArg(1), Target,
                                     OperatorCall->getExprLoc(), Out))
        return Out;
      Errors.push_back(CurrentFn->Name + ": unsupported aggregate assignment");
      return Out;
    }
  }
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const FunctionDecl *Callee = CE->getDirectCallee()) {
      if ((InGhost || CurrentFn->IsProof) && !calleeIsProof(Callee)) {
        Errors.push_back(CurrentFn->Name +
                         ": proof-only code cannot call executable functions");
        return Out;
      }
      if (calleeIsSpec(Callee)) {
        Errors.push_back(CurrentFn->Name +
                         ": bare spec-call statement is unsupported");
        return Out;
      }
      if (functionContract(Callee)) {
        std::vector<std::unique_ptr<VExpr>> Args;
        convertExecCallArgs(CE, Out, Args);
        bool IsProof = calleeIsProof(Callee);
        Out.push_back(std::make_unique<VCallStmt>(
            Callee->getNameAsString(), functionIdentity(Callee),
            std::move(Args), "", CE->getExprLoc(), IsProof));
      } else {
        Errors.push_back(
            CurrentFn->Name +
            ": call to function without a verification contract: " +
            Callee->getNameAsString());
      }
    } else {
      Errors.push_back(CurrentFn->Name +
                       ": indirect function calls are unsupported");
    }
    return Out;
  }
  if (const auto *GB = dyn_cast<GhostBlockStmt>(S)) {
    bool SavedGhost = InGhost;
    InGhost = true;
    auto Body = convertStmt(GB->getBody());
    InGhost = SavedGhost;
    Out.push_back(
        std::make_unique<VGhostBlockStmt>(std::move(Body), GB->getBeginLoc()));
    return Out;
  }
  if (const auto *RW = dyn_cast<RevealWithFuelStmt>(S)) {
    std::string SpecIdentity = specIdentityFromExpr(RW->getFunction());
    if (SpecIdentity.empty()) {
      Errors.push_back(CurrentFn->Name +
                       ": reveal_with_fuel target must resolve to exactly one "
                       "spec function");
      return Out;
    }
    unsigned FuelVal = 1;
    if (const auto *IL = dyn_cast<IntegerLiteral>(RW->getFuel()))
      FuelVal = static_cast<unsigned>(IL->getValue().getZExtValue());
    if (CurrentFn) {
      CurrentFn->SpecFuel[SpecIdentity] =
          std::max(CurrentFn->SpecFuel[SpecIdentity], FuelVal);
      CurrentFn->RevealedSpecs.insert(SpecIdentity);
    }
    Out.push_back(std::make_unique<VRevealWithFuelStmt>(SpecIdentity, FuelVal,
                                                        RW->getBeginLoc()));
    return Out;
  }
  if (const auto *H = dyn_cast<HideSpecStmt>(S)) {
    std::string SpecIdentity = specIdentityFromExpr(H->getFunction());
    if (SpecIdentity.empty()) {
      Errors.push_back(CurrentFn->Name +
                       ": hide target must resolve to exactly one spec "
                       "function");
      return Out;
    }
    if (CurrentFn)
      CurrentFn->HiddenSpecs.insert(SpecIdentity);
    Out.push_back(
        std::make_unique<VHideSpecStmt>(SpecIdentity, H->getBeginLoc()));
    return Out;
  }
  if (const auto *R = dyn_cast<RevealSpecStmt>(S)) {
    std::string SpecIdentity = specIdentityFromExpr(R->getFunction());
    if (SpecIdentity.empty()) {
      Errors.push_back(CurrentFn->Name +
                       ": reveal target must resolve to exactly one spec "
                       "function");
      return Out;
    }
    if (CurrentFn) {
      CurrentFn->RevealedSpecs.insert(SpecIdentity);
      CurrentFn->SpecFuel[SpecIdentity] =
          std::max(CurrentFn->SpecFuel[SpecIdentity], 1u);
    }
    Out.push_back(
        std::make_unique<VRevealSpecStmt>(SpecIdentity, R->getBeginLoc()));
    return Out;
  }
  if (const auto *CA = dyn_cast<ContractAssertStmt>(S)) {
    bool SavedContract = InContractExpression;
    InContractExpression = true;
    if (auto C = convertExpr(CA->getCond()))
      Out.push_back(std::make_unique<VContractAssertStmt>(std::move(C),
                                                          CA->getBeginLoc()));
    InContractExpression = SavedContract;
    return Out;
  }
  if (const auto *Delete = dyn_cast<CXXDeleteExpr>(S)) {
    if (LoopDepth != 0) {
      Errors.push_back(CurrentFn->Name +
                       ": dynamic deallocation inside loops is unsupported");
      return Out;
    }
    if (InGhost || CurrentFn->IsSpec || CurrentFn->IsProof) {
      Errors.push_back(CurrentFn->Name +
                       ": dynamic deallocation requires executable code");
      return Out;
    }
    if (Delete->isArrayForm()) {
      Errors.push_back(CurrentFn->Name + ": delete[] is unsupported");
      return Out;
    }
    const FunctionDecl *OperatorDelete = Delete->getOperatorDelete();
    if (!OperatorDelete ||
        !OperatorDelete->isReplaceableGlobalAllocationFunction()) {
      Errors.push_back(CurrentFn->Name +
                       ": custom or placement deallocation is unsupported");
      return Out;
    }
    const VarDecl *PointerDecl = directDynamicPointer(Delete->getArgument());
    if (!PointerDecl) {
      Errors.push_back(CurrentFn->Name +
                       ": delete requires a direct pointer produced by a "
                       "supported new-expression");
      return Out;
    }
    auto Pointer = convertExpr(Delete->getArgument());
    if (Pointer) {
      CurrentFn->UsesDynamicStorage = true;
      Out.push_back(std::make_unique<VFreeStmt>(std::move(Pointer),
                                                Delete->getBeginLoc()));
    }
    return Out;
  }
  if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->isAssignmentOp()) {
      if (!ghostAssignmentAllowed(BO->getLHS())) {
        Errors.push_back(CurrentFn->Name +
                         ": ghost code cannot modify executable state");
        return Out;
      }
      const auto *DirectLHS =
          dyn_cast<DeclRefExpr>(BO->getLHS()->IgnoreParenImpCasts());
      const auto *DirectTarget =
          DirectLHS ? dyn_cast<VarDecl>(DirectLHS->getDecl()) : nullptr;
      const auto *PointerCall =
          BO->getOpcode() == BO_Assign
              ? dyn_cast<CallExpr>(BO->getRHS()->IgnoreParenImpCasts())
              : nullptr;
      const FunctionDecl *PointerCallee =
          PointerCall ? PointerCall->getDirectCallee() : nullptr;
      if (LoopDepth == 0 && DirectTarget &&
          DirectTarget->getType()->isPointerType() &&
          DynamicPointers.count(DirectTarget) &&
          referencesDynamicPointer(BO->getRHS()) && PointerCallee &&
          PointerCallee->getReturnType()->isPointerType() &&
          Ctx.hasSameUnqualifiedType(
              DirectTarget->getType()->getPointeeType(),
              PointerCallee->getReturnType()->getPointeeType()) &&
          functionContract(PointerCallee) && !calleeIsSpec(PointerCallee) &&
          !calleeIsProof(PointerCallee)) {
        std::vector<std::unique_ptr<VExpr>> Args;
        convertExecCallArgs(PointerCall, Out, Args);
        const std::string &Provenance =
            DynamicPointerProvenanceVariables.at(DirectTarget);
        Out.push_back(std::make_unique<VCallStmt>(
            PointerCallee->getNameAsString(), functionIdentity(PointerCallee),
            std::move(Args), valueName(DirectTarget), BO->getExprLoc(), false,
            Provenance));
        markInitialized(DirectTarget);
        return Out;
      }
      if (BO->getOpcode() == BO_Assign && DirectTarget &&
          DirectTarget->getType()->isPointerType() &&
          (DynamicPointers.count(DirectTarget) ||
           referencesDynamicPointer(BO->getRHS()))) {
        appendDynamicPointerAssignment(DirectTarget, BO->getRHS(),
                                       BO->getExprLoc(), Out);
        return Out;
      }
      if (BO->getRHS()->getType()->isPointerType() &&
          referencesDynamicPointer(BO->getRHS())) {
        Errors.push_back(CurrentFn->Name +
                         ": copying a dynamic-storage pointer is unsupported");
        return Out;
      }
      if (BO->getOpcode() == BO_Assign &&
          BO->getLHS()->getType()->isRecordType()) {
        const Expr *LHS = BO->getLHS()->IgnoreParenImpCasts();
        const auto *DRE = dyn_cast<DeclRefExpr>(LHS);
        const auto *Target = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
        const Expr *RHS = BO->getRHS()->IgnoreParenImpCasts();
        if (Target) {
          if (const auto *Call = dyn_cast<CallExpr>(RHS)) {
            const FunctionDecl *Callee = Call->getDirectCallee();
            if (Callee && functionContract(Callee) && !calleeIsSpec(Callee) &&
                !calleeIsProof(Callee)) {
              std::vector<std::unique_ptr<VExpr>> Args;
              convertExecCallArgs(Call, Out, Args);
              Out.push_back(std::make_unique<VCallStmt>(
                  Callee->getNameAsString(), functionIdentity(Callee),
                  std::move(Args), valueName(Target), BO->getExprLoc(), false));
              markInitialized(Target);
              return Out;
            }
          }
          if (const auto *Init = dyn_cast<InitListExpr>(RHS))
            if (appendRecordInitializer(Init, Target, BO->getExprLoc(), Out))
              return Out;
          if (appendRecordCopy(RHS, Target, BO->getExprLoc(), Out))
            return Out;
        }
        Errors.push_back(CurrentFn->Name +
                         ": unsupported aggregate assignment");
        return Out;
      }
      if (BO->getOpcode() == BO_Assign) {
        const auto *Call =
            dyn_cast<CallExpr>(BO->getRHS()->IgnoreParenImpCasts());
        const FunctionDecl *Callee = Call ? Call->getDirectCallee() : nullptr;
        if (Callee && functionContract(Callee) && !calleeIsSpec(Callee) &&
            !calleeIsProof(Callee)) {
          std::vector<std::unique_ptr<VExpr>> Args;
          convertExecCallArgs(Call, Out, Args);
          const std::string Tmp =
              "__assignment_call_" + std::to_string(++NestedCallId);
          Out.push_back(std::make_unique<VCallStmt>(
              Callee->getNameAsString(), functionIdentity(Callee),
              std::move(Args), Tmp, BO->getExprLoc(), false));
          VType Target =
              VType::fromQualType(BO->getLHS()->getType(), IntMode, Ctx);
          auto Value = convertCallResultValue(Tmp, Callee->getReturnType(),
                                              Target, BO->getExprLoc());
          appendAssignment(BO->getLHS(), std::move(Value), BO->getExprLoc(),
                           Out);
          return Out;
        }
      }
      auto Value = convertAssignmentValue(BO);
      appendAssignment(BO->getLHS(), std::move(Value), BO->getExprLoc(), Out);
    } else
      Errors.push_back(CurrentFn->Name + ": unsupported expression statement");
    return Out;
  }
  if (const auto *U = dyn_cast<UnaryOperator>(S)) {
    if (U->isIncrementDecrementOp()) {
      if (!U->getSubExpr()->getType()->isIntegerType()) {
        Errors.push_back(CurrentFn->Name +
                         ": pointer increment/decrement is unsupported");
        return Out;
      }
      auto Current = convertExpr(U->getSubExpr());
      if (!Current)
        return Out;
      QualType TargetQualType = U->getSubExpr()->getType();
      QualType ComputationQualType = TargetQualType;
      if (Ctx.isPromotableIntegerType(TargetQualType))
        ComputationQualType = Ctx.getPromotedIntegerType(TargetQualType);
      VType TargetTy = VType::fromQualType(TargetQualType, IntMode, Ctx);
      VType ComputationTy =
          VType::fromQualType(ComputationQualType, IntMode, Ctx);
      auto SameType = [](const VType &A, const VType &B) {
        return A.Kind == B.Kind && A.IntMode == B.IntMode &&
               A.IsSigned == B.IsSigned && A.BitWidth == B.BitWidth;
      };
      if (!SameType(Current->Ty, ComputationTy)) {
        VType SourceTy = Current->Ty;
        Current = std::make_unique<VCastExpr>(std::move(Current), SourceTy,
                                              ComputationTy, U->getExprLoc());
      }
      auto One =
          std::make_unique<VLiteralExpr>(1, ComputationTy, U->getExprLoc());
      VBinOp Op = U->isIncrementOp() ? VBinOp::Add : VBinOp::Sub;
      std::unique_ptr<VExpr> Value =
          std::make_unique<VBinOpExpr>(Op, std::move(Current), std::move(One),
                                       ComputationTy, U->getExprLoc());
      if (!SameType(ComputationTy, TargetTy))
        Value = std::make_unique<VCastExpr>(std::move(Value), ComputationTy,
                                            TargetTy, U->getExprLoc());
      appendAssignment(U->getSubExpr(), std::move(Value), U->getExprLoc(), Out);
    } else
      Errors.push_back(CurrentFn->Name +
                       ": unsupported unary expression statement");
    return Out;
  }
  if (const auto *CE = dyn_cast<CStyleCastExpr>(S)) {
    const Expr *Sub = CE->getSubExpr()->IgnoreParenImpCasts();
    if (CE->getCastKind() == CK_ToVoid && isa<DeclRefExpr>(Sub) &&
        !Sub->getType().isVolatileQualified())
      return Out;
    Errors.push_back(CurrentFn->Name +
                     ": unsupported discarded-value expression");
    return Out;
  }
  if (const auto *DS = dyn_cast<DeclStmt>(S)) {
    for (const Decl *D : DS->decls()) {
      const auto *VD = dyn_cast<VarDecl>(D);
      if (!VD) {
        Errors.push_back(CurrentFn->Name +
                         ": unsupported declaration statement");
        continue;
      }
      if (!VD->hasLocalStorage()) {
        Errors.push_back(CurrentFn->Name +
                         ": static local variables are unsupported");
        continue;
      }
      if (!DeclaredValueNames.insert(VD->getNameAsString()).second) {
        Errors.push_back(CurrentFn->Name +
                         ": local variable shadowing is unsupported: " +
                         VD->getNameAsString());
        continue;
      }
      if (InGhost)
        GhostLocals.insert(VD);
      if (!VD->hasInit())
        continue;
      if (const auto *New =
              dyn_cast<CXXNewExpr>(VD->getInit()->IgnoreParenImpCasts())) {
        if (LoopDepth != 0) {
          Errors.push_back(CurrentFn->Name +
                           ": dynamic allocation inside loops is unsupported");
          continue;
        }
        if (InGhost || CurrentFn->IsSpec || CurrentFn->IsProof) {
          Errors.push_back(CurrentFn->Name +
                           ": dynamic allocation requires executable code");
          continue;
        }
        bool HasPointerParam = false;
        for (const auto &Param : CurrentFn->Params)
          HasPointerParam |= Param.second.Kind == VTypeKind::Ptr;
        if (HasPointerParam) {
          Errors.push_back(
              CurrentFn->Name +
              ": dynamic allocation in functions with pointer parameters is "
              "not yet supported");
          continue;
        }
        bool IsNothrow = false;
        const FunctionDecl *OperatorNew = New->getOperatorNew();
        if (New->isArray() || New->getNumPlacementArgs() != 0 || !OperatorNew ||
            !OperatorNew->isReplaceableGlobalAllocationFunction(nullptr,
                                                                &IsNothrow) ||
            IsNothrow || New->shouldNullCheckAllocation()) {
          Errors.push_back(CurrentFn->Name +
                           ": only ordinary throwing scalar new is supported");
          continue;
        }
        QualType Allocated = New->getAllocatedType();
        if (!VD->getType()->isPointerType() ||
            !Ctx.hasSameUnqualifiedType(VD->getType()->getPointeeType(),
                                        Allocated)) {
          Errors.push_back(
              CurrentFn->Name +
              ": new result must directly initialize a matching typed pointer");
          continue;
        }
        if ((!Allocated->isIntegerType() && !Allocated->isEnumeralType()) ||
            Allocated.isVolatileQualified() || Allocated->isAtomicType() ||
            Allocated->isIncompleteType()) {
          Errors.push_back(
              CurrentFn->Name +
              ": new currently supports only complete non-volatile scalar "
              "integer objects");
          continue;
        }
        const uint64_t Size = Ctx.getTypeSizeInChars(Allocated).getQuantity();
        const uint64_t Align = Ctx.getTypeAlignInChars(Allocated).getQuantity();
        if (Size == 0 || Size > 256 || Align == 0) {
          Errors.push_back(CurrentFn->Name +
                           ": unsupported dynamic object size or alignment");
          continue;
        }
        std::unique_ptr<VExpr> Initializer;
        if (const Expr *Init = New->getInitializer())
          Initializer = convertExpr(Init);
        if (New->hasInitializer() && !Initializer)
          continue;
        auto Provenance = DynamicPointerProvenanceVariables.find(VD);
        if (Provenance == DynamicPointerProvenanceVariables.end())
          Provenance =
              DynamicPointerProvenanceVariables
                  .emplace(VD, "__cppverify_pointer_provenance_" +
                                   std::to_string(++DynamicProvenanceId))
                  .first;
        const std::string &ProvenanceVariable = Provenance->second;
        DynamicPointers.insert(VD);
        CurrentFn->UsesDynamicStorage = true;
        Out.push_back(std::make_unique<VAllocateStmt>(
            valueName(VD), ProvenanceVariable,
            VType::fromQualType(Allocated, IntMode, Ctx),
            std::move(Initializer), Size, Align, VD->getBeginLoc()));
        markInitialized(VD);
        continue;
      }
      if (LoopDepth == 0 && VD->getType()->isPointerType() &&
          DynamicPointers.count(VD)) {
        const auto *Call =
            dyn_cast<CallExpr>(VD->getInit()->IgnoreParenImpCasts());
        const FunctionDecl *Callee = Call ? Call->getDirectCallee() : nullptr;
        if (Callee && Callee->getReturnType()->isPointerType() &&
            Ctx.hasSameUnqualifiedType(
                VD->getType()->getPointeeType(),
                Callee->getReturnType()->getPointeeType()) &&
            functionContract(Callee) && !calleeIsSpec(Callee) &&
            !calleeIsProof(Callee)) {
          std::vector<std::unique_ptr<VExpr>> Args;
          convertExecCallArgs(Call, Out, Args);
          const std::string &Provenance =
              DynamicPointerProvenanceVariables.at(VD);
          Out.push_back(std::make_unique<VCallStmt>(
              Callee->getNameAsString(), functionIdentity(Callee),
              std::move(Args), valueName(VD), VD->getBeginLoc(), false,
              Provenance));
          markInitialized(VD);
          continue;
        }
      }
      if (VD->getType()->isPointerType() &&
          referencesDynamicPointer(VD->getInit())) {
        appendDynamicPointerAssignment(VD, VD->getInit(), VD->getBeginLoc(),
                                       Out);
        continue;
      }
      if (const auto *CE = dyn_cast<CXXConstructExpr>(VD->getInit())) {
        const CXXConstructorDecl *Ctor = CE->getConstructor();
        if (CE->getNumArgs() == 0 && Ctor->isDefaultConstructor() &&
            Ctor->isTrivial())
          continue;
      }
      if (const auto *CE =
              dyn_cast<CallExpr>(VD->getInit()->IgnoreParenImpCasts())) {
        if (const FunctionDecl *Callee = CE->getDirectCallee()) {
          if (calleeIsSpec(Callee)) {
            if (auto Val = convertExpr(VD->getInit())) {
              Out.push_back(std::make_unique<VAssignStmt>(
                  VD->getNameAsString(), std::move(Val), VD->getBeginLoc()));
              markInitialized(VD);
            }
            continue;
          }
          if (functionContract(Callee)) {
            std::vector<std::unique_ptr<VExpr>> Args;
            convertExecCallArgs(CE, Out, Args);
            const bool RecordResult = VD->getType()->isRecordType();
            const std::string ResultTarget =
                RecordResult ? VD->getNameAsString()
                             : "__local_call_" + std::to_string(++NestedCallId);
            Out.push_back(std::make_unique<VCallStmt>(
                Callee->getNameAsString(), functionIdentity(Callee),
                std::move(Args), ResultTarget, VD->getBeginLoc(),
                calleeIsProof(Callee)));
            if (!RecordResult) {
              VType Target = VType::fromQualType(VD->getType(), IntMode, Ctx);
              if (auto Value = convertCallResultValue(
                      ResultTarget, Callee->getReturnType(), Target,
                      VD->getBeginLoc()))
                Out.push_back(std::make_unique<VAssignStmt>(
                    VD->getNameAsString(), std::move(Value),
                    VD->getBeginLoc()));
            }
            markInitialized(VD);
            continue;
          }
        }
      }
      if (VD->getType()->isRecordType()) {
        const Expr *Init = VD->getInit()->IgnoreParenImpCasts();
        if (const auto *List = dyn_cast<InitListExpr>(Init))
          if (appendRecordInitializer(List, VD, VD->getBeginLoc(), Out))
            continue;
        if (appendRecordCopy(Init, VD, VD->getBeginLoc(), Out))
          continue;
        Errors.push_back(CurrentFn->Name +
                         ": aggregate initialization and copying are "
                         "unsupported");
        continue;
      }
      auto Val = convertExpr(VD->getInit());
      if (Val) {
        Out.push_back(std::make_unique<VAssignStmt>(
            VD->getNameAsString(), std::move(Val), VD->getBeginLoc()));
        markInitialized(VD);
      }
    }
    return Out;
  }
  Errors.push_back(CurrentFn->Name +
                   ": unsupported statement: " + S->getStmtClassName());
  return Out;
}