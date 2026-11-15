//===--- VHash.cpp - Semantic digests of Layer 1 functions ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "VHash.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Endian.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SHA256.h"

using namespace clang;
using namespace clang::verify;

// A node that gains a member changes size on the platform below, which
// stops the build here until the member is written (or found to be a
// position) and the size is updated with VFunctionDigestVersion.
#if defined(__x86_64__) && defined(__linux__) && defined(__GLIBCXX__) &&       \
    !defined(_GLIBCXX_DEBUG) && !defined(_GLIBCXX_ASSERTIONS)
#define CPPVERIFY_DIGEST_COVERS(Type, Size)                                    \
  static_assert(sizeof(Type) == Size,                                          \
                #Type " changed: update its digest in VHash.cpp")
#else
#define CPPVERIFY_DIGEST_COVERS(Type, Size)
#endif

namespace {

CPPVERIFY_DIGEST_COVERS(VType, 152);
CPPVERIFY_DIGEST_COVERS(VExpr, 184);
CPPVERIFY_DIGEST_COVERS(VLiteralExpr, 216);
CPPVERIFY_DIGEST_COVERS(VVarExpr, 312);
CPPVERIFY_DIGEST_COVERS(VBinOpExpr, 200);
CPPVERIFY_DIGEST_COVERS(VUnaryOpExpr, 288);
CPPVERIFY_DIGEST_COVERS(VCastExpr, 352);
CPPVERIFY_DIGEST_COVERS(VLoadExpr, 232);
CPPVERIFY_DIGEST_COVERS(VResultExpr, 184);
CPPVERIFY_DIGEST_COVERS(VOldExpr, 192);
CPPVERIFY_DIGEST_COVERS(VConditionalExpr, 208);
CPPVERIFY_DIGEST_COVERS(VQuantifiedExpr, 392);
CPPVERIFY_DIGEST_COVERS(VHeapStoreExpr, 264);
CPPVERIFY_DIGEST_COVERS(VHeapFrameExpr, 272);
CPPVERIFY_DIGEST_COVERS(VFieldAccessExpr, 224);
CPPVERIFY_DIGEST_COVERS(VSpecCallExpr, 312);
CPPVERIFY_DIGEST_COVERS(VOverflowCheckExpr, 200);
CPPVERIFY_DIGEST_COVERS(VRequireExpr, 200);
CPPVERIFY_DIGEST_COVERS(VStmt, 16);
CPPVERIFY_DIGEST_COVERS(VAssignStmt, 64);
CPPVERIFY_DIGEST_COVERS(VStoreStmt, 40);
CPPVERIFY_DIGEST_COVERS(VAllocateStmt, 264);
CPPVERIFY_DIGEST_COVERS(VEndLifetimeStmt, 88);
CPPVERIFY_DIGEST_COVERS(VFreeStmt, 24);
CPPVERIFY_DIGEST_COVERS(VIfStmt, 80);
CPPVERIFY_DIGEST_COVERS(VWhileStmt, 144);
CPPVERIFY_DIGEST_COVERS(VCallStmt, 184);
CPPVERIFY_DIGEST_COVERS(VAssertStmt, 64);
CPPVERIFY_DIGEST_COVERS(VAssumeStmt, 24);
CPPVERIFY_DIGEST_COVERS(VReturnStmt, 24);
CPPVERIFY_DIGEST_COVERS(VSeqStmt, 40);
CPPVERIFY_DIGEST_COVERS(VHavocStmt, 48);
CPPVERIFY_DIGEST_COVERS(VGhostBlockStmt, 40);
CPPVERIFY_DIGEST_COVERS(VRevealWithFuelStmt, 56);
CPPVERIFY_DIGEST_COVERS(VHideSpecStmt, 48);
CPPVERIFY_DIGEST_COVERS(VRevealSpecStmt, 48);
CPPVERIFY_DIGEST_COVERS(VContractAssertStmt, 48);
CPPVERIFY_DIGEST_COVERS(VBreakStmt, 16);
CPPVERIFY_DIGEST_COVERS(VContinueStmt, 16);

class Digest {
  llvm::SHA256 Hash;
  std::set<std::string> &References;
  VDigestScope Scope;
  llvm::function_ref<std::string(SourceLocation)> Place;

public:
  Digest(std::set<std::string> &References, VDigestScope Scope,
         llvm::function_ref<std::string(SourceLocation)> Place)
      : References(References), Scope(Scope), Place(Place) {}

  std::string result() {
    return llvm::toHex(Hash.final(), /*LowerCase=*/true);
  }

  void number(uint64_t Value) {
    char Bytes[8];
    llvm::support::endian::write64le(Bytes, Value);
    Hash.update(llvm::StringRef(Bytes, 8));
  }
  void flag(bool Value) { number(Value); }
  void text(llvm::StringRef Value) {
    number(Value.size());
    Hash.update(Value);
  }
  /// Whether there is a position, and with Place where it is.
  void present(SourceLocation Loc) {
    flag(Loc.isValid());
    if (Place && Loc.isValid())
      text(Place(Loc));
  }
  void present(SourceRange Range) {
    present(Range.getBegin());
    present(Range.getEnd());
  }
  void present(const SourceSpan &Span) {
    present(Span.Loc);
    present(Span.BeginLoc);
    present(Span.EndLoc);
  }
  void reference(const std::string &Identity) {
    text(Identity);
    if (!Identity.empty())
      References.insert(Identity);
  }
  void references(const std::set<std::string> &Identities) {
    number(Identities.size());
    for (const std::string &Identity : Identities)
      reference(Identity);
  }
  void texts(const std::set<std::string> &Values) {
    number(Values.size());
    for (const std::string &Value : Values)
      text(Value);
  }

  void type(const VType &Ty) {
    const auto &[Kind, IntMode, IsSigned, BitWidth, PointeeSizeBytes,
                 ObjectSizeBytes, ObjectAlignBytes, ArrayCount,
                 ArrayStrideBytes, TypeIdentity, EnumMin, EnumMax] = Ty;
    number(static_cast<uint64_t>(Kind));
    number(static_cast<uint64_t>(IntMode));
    flag(IsSigned);
    number(BitWidth);
    number(PointeeSizeBytes);
    number(ObjectSizeBytes);
    number(ObjectAlignBytes);
    number(ArrayCount);
    number(ArrayStrideBytes);
    text(TypeIdentity);
    text(EnumMin);
    text(EnumMax);
  }

  void layout(const VObjectLayout &Layout) {
    const auto &[Kind, TypeIdentity, DisplayName, SizeBytes, AlignBytes,
                 ElementCount, StrideBytes, Leaves] = Layout;
    number(static_cast<uint64_t>(Kind));
    text(TypeIdentity);
    text(DisplayName);
    number(SizeBytes);
    number(AlignBytes);
    number(ElementCount);
    number(StrideBytes);
    number(Leaves.size());
    for (const VObjectLeaf &Leaf : Leaves) {
      const auto &[Path, Ty, OffsetBytes, LeafSize, LeafAlign, Repeats, Loc] =
          Leaf;
      text(Path);
      type(Ty);
      number(OffsetBytes);
      number(LeafSize);
      number(LeafAlign);
      number(Repeats.size());
      for (const VObjectRepeat &Repeat : Repeats) {
        const auto &[Count, Stride] = Repeat;
        number(Count);
        number(Stride);
      }
      present(Loc);
    }
  }

  void exprs(const std::vector<std::unique_ptr<VExpr>> &Exprs) {
    number(Exprs.size());
    for (const auto &E : Exprs)
      expr(E.get());
  }

  void expr(const VExpr *E) {
    if (!E) {
      number(~0ULL);
      return;
    }
    number(E->K);
    type(E->Ty);
    present(E->Loc);
    present(E->BeginLoc);
    present(E->EndLoc);
    switch (E->K) {
    case VExpr::Literal:
      text(static_cast<const VLiteralExpr *>(E)->Value);
      return;
    case VExpr::Var: {
      const auto *V = static_cast<const VVarExpr *>(E);
      text(V->Name);
      text(V->ProvenanceVariable);
      flag(V->Origins.has_value());
      if (V->Origins) {
        number(V->Origins->size());
        for (const std::string &Origin : *V->Origins)
          text(Origin);
      }
      text(V->OriginCompanion);
      return;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      number(static_cast<uint64_t>(B->Op));
      expr(B->Lhs.get());
      expr(B->Rhs.get());
      return;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      number(static_cast<uint64_t>(U->Op));
      expr(U->Operand.get());
      text(U->AllocationHeapVar);
      text(U->LivenessHeapVar);
      text(U->InitializationHeapVar);
      return;
    }
    case VExpr::Cast: {
      const auto *C = static_cast<const VCastExpr *>(E);
      type(C->FromTy);
      expr(C->Inner.get());
      flag(C->IsTrigger);
      return;
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      text(L->HeapVar);
      expr(L->Ptr.get());
      expr(L->AccessCondition.get());
      return;
    }
    case VExpr::Result:
      return;
    case VExpr::Old:
      expr(static_cast<const VOldExpr *>(E)->Inner.get());
      return;
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      expr(C->Cond.get());
      expr(C->Then.get());
      expr(C->Else.get());
      return;
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(E);
      text(Q->Binder);
      type(Q->BinderType);
      expr(Q->Lo.get());
      expr(Q->Hi.get());
      expr(Q->Body.get());
      return;
    }
    case VExpr::HeapStore: {
      const auto *S = static_cast<const VHeapStoreExpr *>(E);
      text(S->HeapBefore);
      text(S->HeapAfter);
      expr(S->Ptr.get());
      expr(S->Val.get());
      return;
    }
    case VExpr::HeapFrame: {
      const auto *F = static_cast<const VHeapFrameExpr *>(E);
      text(F->HeapBefore);
      text(F->HeapAfter);
      number(F->Regions.size());
      for (const auto &[Base, Count] : F->Regions) {
        expr(Base.get());
        expr(Count.get());
      }
      return;
    }
    case VExpr::FieldAccess: {
      const auto *F = static_cast<const VFieldAccessExpr *>(E);
      expr(F->Base.get());
      text(F->Field);
      return;
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      text(C->Callee);
      reference(C->CalleeIdentity);
      exprs(C->Args);
      flag(C->ReadsHeap);
      text(C->HeapVar);
      return;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      number(static_cast<uint64_t>(O->Op));
      expr(O->Lhs.get());
      expr(O->Rhs.get());
      return;
    }
    case VExpr::Require: {
      const auto *R = static_cast<const VRequireExpr *>(E);
      expr(R->Cond.get());
      number(R->ProofKind);
      return;
    }
    }
    llvm_unreachable("unknown VExpr kind");
  }

  void checks(const std::vector<VMemoryCheck> &Checks) {
    number(Checks.size());
    for (const VMemoryCheck &Check : Checks) {
      const auto &[Kind, Cond] = Check;
      number(static_cast<uint64_t>(Kind));
      expr(Cond.get());
    }
  }
  void checkLists(const std::vector<std::vector<VMemoryCheck>> &Lists) {
    number(Lists.size());
    for (const auto &List : Lists)
      checks(List);
  }
  void footprints(const std::vector<VFootprint> &Footprints) {
    number(Footprints.size());
    for (const VFootprint &Footprint : Footprints) {
      const auto &[Target, Count, ElementSize] = Footprint;
      expr(Target.get());
      expr(Count.get());
      number(ElementSize);
    }
  }

  void stmts(const std::vector<std::unique_ptr<VStmt>> &Stmts) {
    number(Stmts.size());
    for (const auto &S : Stmts)
      stmt(S.get());
  }

  void stmt(const VStmt *S) {
    if (!S) {
      number(~0ULL);
      return;
    }
    number(S->K);
    present(S->Loc);
    switch (S->K) {
    case VStmt::Assign: {
      const auto *A = static_cast<const VAssignStmt *>(S);
      text(A->Target);
      expr(A->Value.get());
      flag(A->IsReferenceBinding);
      return;
    }
    case VStmt::Store: {
      const auto *St = static_cast<const VStoreStmt *>(S);
      expr(St->Ptr.get());
      expr(St->Value.get());
      expr(St->AccessCondition.get());
      return;
    }
    case VStmt::Allocate: {
      const auto *A = static_cast<const VAllocateStmt *>(S);
      text(A->Target);
      text(A->ProvenanceTarget);
      type(A->AllocatedType);
      expr(A->Initializer.get());
      number(A->SizeBytes);
      number(A->AlignBytes);
      flag(A->IsAutomatic);
      return;
    }
    case VStmt::EndLifetime: {
      const auto *L = static_cast<const VEndLifetimeStmt *>(S);
      text(L->Target);
      text(L->ProvenanceTarget);
      flag(L->IsFunctionExit);
      return;
    }
    case VStmt::Free:
      expr(static_cast<const VFreeStmt *>(S)->Ptr.get());
      return;
    case VStmt::If: {
      const auto *I = static_cast<const VIfStmt *>(S);
      expr(I->Cond.get());
      stmts(I->Then);
      stmts(I->Else);
      flag(I->IsLoopUnroll);
      number(I->LoopUnrollIteration);
      return;
    }
    case VStmt::While: {
      const auto *W = static_cast<const VWhileStmt *>(S);
      expr(W->Cond.get());
      exprs(W->Invariants);
      exprs(W->Decreases);
      footprints(W->Modifies);
      checkLists(W->InvariantChecks);
      stmts(W->Body);
      return;
    }
    case VStmt::Call: {
      const auto *C = static_cast<const VCallStmt *>(S);
      text(C->Callee);
      reference(C->CalleeIdentity);
      exprs(C->Args);
      text(C->ResultTarget);
      text(C->ResultProvenanceTarget);
      flag(C->IsProofCall);
      flag(C->InlinesHelper);
      present(C->CallSite);
      return;
    }
    case VStmt::Assert: {
      const auto *A = static_cast<const VAssertStmt *>(S);
      expr(A->Cond.get());
      number(static_cast<uint64_t>(A->ProofKind));
      text(A->Note);
      return;
    }
    case VStmt::Assume:
      expr(static_cast<const VAssumeStmt *>(S)->Cond.get());
      return;
    case VStmt::Return:
      expr(static_cast<const VReturnStmt *>(S)->Value.get());
      return;
    case VStmt::Seq:
      stmts(static_cast<const VSeqStmt *>(S)->Stmts);
      return;
    case VStmt::Havoc:
      text(static_cast<const VHavocStmt *>(S)->Target);
      return;
    case VStmt::GhostBlock:
      stmts(static_cast<const VGhostBlockStmt *>(S)->Body);
      return;
    case VStmt::RevealWithFuel: {
      const auto *R = static_cast<const VRevealWithFuelStmt *>(S);
      reference(R->SpecFunction);
      number(R->Fuel);
      return;
    }
    case VStmt::HideSpec:
      reference(static_cast<const VHideSpecStmt *>(S)->SpecFunction);
      return;
    case VStmt::RevealSpec:
      reference(static_cast<const VRevealSpecStmt *>(S)->SpecFunction);
      return;
    case VStmt::ContractAssert: {
      const auto *A = static_cast<const VContractAssertStmt *>(S);
      expr(A->Cond.get());
      checks(A->MemoryChecks);
      return;
    }
    case VStmt::Break:
    case VStmt::Continue:
      return;
    }
    llvm_unreachable("unknown VStmt kind");
  }

  void kinds(const std::vector<ProofObligationKind> &Kinds) {
    number(Kinds.size());
    for (ProofObligationKind Kind : Kinds)
      number(static_cast<uint64_t>(Kind));
  }
  void typed(const std::vector<std::pair<std::string, VType>> &Names) {
    number(Names.size());
    for (const auto &[Name, Ty] : Names) {
      text(Name);
      type(Ty);
    }
  }
  void named(
      const std::vector<std::pair<std::string, std::unique_ptr<VExpr>>> &List) {
    number(List.size());
    for (const auto &[Name, E] : List) {
      text(Name);
      expr(E.get());
    }
  }

  void function(const VFunction &Fn) {
    // Every member, in the order of its declaration: a member added to
    // VFunction does not compile here until it is named.
    const auto &[Name,
                 Identity,
                 ReturnType,
                 IntMode,
                 IsSpec,
                 IsProof,
                 IsConstexprSpec,
                 ReadsHeap,
                 RequiresCallDefinedness,
                 IsExternalContract,
                 IsTrusted,
                 IsConstructor,
                 DeclLoc,
                 Extent,
                 InlinedExtents,
                 PrivateObjects,
                 NeedsDecreasesCheck,
                 DivergenceLoc,
                 DivergenceDeclared,
                 UnmeasuredLoop,
                 ObjectModel,
                 RecursionGroup,
                 Cluster,
                 SpecDependencies,
                 Reads,
                 Domain,
                 Uninterpreted,
                 UnsupportedConstruct,
                 IsChoice,
                 IsBuiltin,
                 IsInlineHelper,
                 WithoutContract,
                 InductiveLoc,
                 Unfolding,
                 InductiveStepOf,
                 InductiveRuleOf,
                 FactsWithheld,
                 TotalExpressions,
                 ClauseProofs,
                 Behaviors,
                 UsesDynamicStorage,
                 FreshOwnedReturn,
                 SpecFuel,
                 HiddenSpecs,
                 RevealedSpecs,
                 Params,
                 SourceVariables,
                 ScalarReferenceParams,
                 RecordParams,
                 FieldParams,
                 ConstAddressParams,
                 OutParameters,
                 BoundedPointers,
                 LendableScalarParams,
                 LendableRecordParams,
                 MayWriteHeap,
                 ReturnedPointers,
                 ReturnFields,
                 ExplicitPreconditionCount,
                 Preconditions,
                 Postconditions,
                 PreconditionChecks,
                 PostconditionChecks,
                 PreconditionKinds,
                 PostconditionKinds,
                 Recommends,
                 Modifies,
                 Aliases,
                 ValidExtents,
                 DisjointAddresses,
                 Decreases,
                 Body,
                 Layouts] = Fn;
    number(VFunctionDigestVersion);
    number(static_cast<uint64_t>(Scope));
    text(Name);
    text(Identity);
    type(ReturnType);
    number(static_cast<uint64_t>(IntMode));
    flag(IsSpec);
    flag(IsProof);
    flag(IsConstexprSpec);
    flag(ReadsHeap);
    flag(RequiresCallDefinedness);
    flag(IsExternalContract);
    flag(IsTrusted);
    flag(IsConstructor);
    present(DeclLoc);
    present(Extent);
    number(InlinedExtents.size());
    for (SourceRange Range : InlinedExtents)
      present(Range);
    exprs(PrivateObjects);
    flag(NeedsDecreasesCheck);
    present(DivergenceLoc);
    flag(DivergenceDeclared);
    present(UnmeasuredLoop);
    flag(ObjectModel);
    references(RecursionGroup);
    references(Cluster);
    references(SpecDependencies);
    number(Reads.size());
    for (const VReadRange &Range : Reads) {
      const auto &[Base, Count, ElementSize] = Range;
      expr(Base.get());
      expr(Count.get());
      number(ElementSize);
    }
    expr(Domain.get());
    flag(Uninterpreted);
    flag(UnsupportedConstruct);
    flag(IsChoice);
    flag(IsBuiltin);
    flag(IsInlineHelper);
    flag(WithoutContract);
    present(InductiveLoc);
    expr(Unfolding.get());
    reference(InductiveStepOf);
    reference(InductiveRuleOf);
    references(FactsWithheld);
    flag(TotalExpressions);
    number(ClauseProofs.size());
    for (const VFunction::ClauseProof &Proof : ClauseProofs) {
      const auto &[Kind, ProofBody, Loc] = Proof;
      number(Kind);
      present(Loc);
      if (Scope == VDigestScope::Whole)
        stmts(ProofBody);
    }
    named(Behaviors);
    flag(UsesDynamicStorage);
    flag(FreshOwnedReturn.has_value());
    if (FreshOwnedReturn) {
      const auto &[AllocatedType, SizeBytes, AlignBytes, MayReturnNull] =
          *FreshOwnedReturn;
      type(AllocatedType);
      number(SizeBytes);
      number(AlignBytes);
      flag(MayReturnNull);
    }
    number(SpecFuel.size());
    for (const auto &[Spec, Fuel] : SpecFuel) {
      reference(Spec);
      number(Fuel);
    }
    references(HiddenSpecs);
    references(RevealedSpecs);
    typed(Params);
    number(SourceVariables.size());
    for (const auto &[Variable, Source] : SourceVariables) {
      const auto &[DisplayName, Ty, Loc, EndLoc, Reference] = Source;
      text(Variable);
      text(DisplayName);
      type(Ty);
      present(Loc);
      present(EndLoc);
      flag(Reference);
    }
    texts(ScalarReferenceParams);
    number(RecordParams.size());
    for (const auto &[Param, Record] : RecordParams) {
      text(Param);
      text(Record);
    }
    named(FieldParams);
    texts(ConstAddressParams);
    texts(OutParameters);
    texts(BoundedPointers);
    texts(LendableScalarParams);
    texts(LendableRecordParams);
    flag(MayWriteHeap);
    flag(ReturnedPointers.has_value());
    if (ReturnedPointers)
      texts(*ReturnedPointers);
    typed(ReturnFields);
    number(ExplicitPreconditionCount);
    exprs(Preconditions);
    exprs(Postconditions);
    checkLists(PreconditionChecks);
    checkLists(PostconditionChecks);
    kinds(PreconditionKinds);
    kinds(PostconditionKinds);
    exprs(Recommends);
    footprints(Modifies);
    number(Aliases.size());
    for (const auto &[First, Second] : Aliases) {
      expr(First.get());
      expr(Second.get());
    }
    number(ValidExtents.size());
    for (const VValidExtent &Extent : ValidExtents) {
      const auto &[Base, PointerType, Length] = Extent;
      text(Base);
      type(PointerType);
      expr(Length.get());
    }
    number(DisjointAddresses.size());
    for (const VDisjointAddresses &Pair : DisjointAddresses) {
      const auto &[First, Second, FirstSizeBytes, SecondSizeBytes] = Pair;
      text(First);
      text(Second);
      number(FirstSizeBytes);
      number(SecondSizeBytes);
    }
    exprs(Decreases);
    if (Scope == VDigestScope::Whole)
      stmts(Body);
    number(Layouts.size());
    for (const VObjectLayout &Layout : Layouts)
      layout(Layout);
  }
};

} // namespace

VFunctionDigest verify::digestVFunction(
    const VFunction &Fn, VDigestScope Scope,
    llvm::function_ref<std::string(SourceLocation)> Place) {
  VFunctionDigest Result;
  Digest D(Result.References, Scope, Place);
  D.function(Fn);
  Result.Hash = D.result();
  return Result;
}
