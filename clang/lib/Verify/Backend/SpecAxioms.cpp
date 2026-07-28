//===--- SpecAxioms.cpp - Verus-style spec defining axioms ----------------===//
#include "SpecAxioms.h"
#include "../Transform/SpecInline.h"
#include "ObligationLowering.h"
#include "llvm/Support/Error.h"

using namespace clang;
using namespace verify;

void verify::collectReferencedSpecs(const VExpr *E,
                                    std::set<std::string> &Out) {
  std::vector<const VSpecCallExpr *> Calls;
  collectSpecCalls(E, Calls);
  for (const VSpecCallExpr *C : Calls)
    Out.insert(C->CalleeIdentity);
}

std::unique_ptr<VExpr> verify::unfoldSpecDefinition(const VFunction &Spec,
                                                    const SpecAxiomContext &Ctx,
                                                    unsigned Fuel) {
  SpecInliner Inliner(Ctx.Functions, Ctx.SpecFuel);
  return Inliner.unfoldDefinition(Spec, Ctx.SpecFuel, Ctx.HiddenSpecs,
                                  Ctx.RevealedSpecs, Fuel);
}

std::unique_ptr<VExpr>
verify::unfoldSpecBodyForAxiom(const VFunction &Spec,
                               const SpecAxiomContext &Ctx) {
  // One step of unfolding (RootFuel = 1) with recursive leaves kept as spec
  // applications. Hidden/revealed sets are intentionally empty so the body is
  // expanded one level regardless of the caller's reveal state.
  SpecInliner Inliner(Ctx.Functions, Ctx.SpecFuel);
  return Inliner.unfoldDefinition(Spec, {}, {}, {}, /*RootFuel=*/1,
                                  /*KeepLeaves=*/true);
}

static LogicSort specLogicSort(const VType &Type, VIntMode Mode) {
  if (Type.Kind == VTypeKind::Bool)
    return LogicSort::boolSort();
  if (Type.Kind == VTypeKind::Ptr)
    return LogicSort::pointer();
  if (Type.Kind != VTypeKind::Int32 && Type.Kind != VTypeKind::Int64)
    return {};
  if (Mode == VIntMode::Math)
    return LogicSort::mathematicalInteger(Type.BitWidth, Type.IsSigned);
  return LogicSort::bitVector(Type.BitWidth, Type.IsSigned);
}

static bool sameLogicSort(const LogicSort &Left, const LogicSort &Right) {
  if (Left.Kind != Right.Kind)
    return false;
  if (Left.Kind == LogicSortKind::MathematicalInteger)
    return true;
  return Left.BitWidth == Right.BitWidth && Left.Signedness == Right.Signedness;
}

static std::unique_ptr<LogicExpr>
coerceDefinition(std::unique_ptr<LogicExpr> Expression, const VType &ResultType,
                 VIntMode ResultMode) {
  const LogicSort Target = specLogicSort(ResultType, ResultMode);
  if (!Expression || Target.Kind == LogicSortKind::Invalid)
    return nullptr;
  if (sameLogicSort(Expression->Sort, Target))
    return Expression;

  LogicExpr::Kind Kind;
  if (Target.Kind == LogicSortKind::BitVector &&
      (Expression->Sort.Kind == LogicSortKind::MathematicalInteger ||
       Expression->Sort.Kind == LogicSortKind::Pointer))
    Kind = LogicExpr::IntToBv;
  else if (Target.Kind == LogicSortKind::MathematicalInteger &&
           Expression->Sort.Kind == LogicSortKind::BitVector)
    Kind = LogicExpr::BvToInt;
  else if (Target.Kind == LogicSortKind::BitVector &&
           Expression->Sort.Kind == LogicSortKind::BitVector)
    Kind = LogicExpr::BvResize;
  else
    return nullptr;

  auto Converted = std::make_unique<LogicExpr>(Kind);
  Converted->Sort = Target;
  Converted->Loc = Expression->Loc;
  Converted->Children.push_back(std::move(Expression));
  return Converted;
}

static void collectReferencedLogicFunctions(const LogicExpr *Expression,
                                            std::set<std::string> &Names) {
  if (!Expression)
    return;
  if (Expression->K == LogicExpr::SpecCall)
    Names.insert(Expression->SpecCallee);
  for (const auto &Child : Expression->Children)
    collectReferencedLogicFunctions(Child.get(), Names);
}

static const VFunction *findSpecFunction(const FunctionMap &Functions,
                                         llvm::StringRef Identity) {
  if (auto It = Functions.find(Identity.str());
      It != Functions.end() && It->second)
    return It->second;
  for (const auto &[Key, Function] : Functions)
    if (Function && Function->Identity == Identity)
      return Function;
  return nullptr;
}

llvm::Error verify::materializeLogicFunctions(ObligationModule &Module,
                                              const SpecAxiomContext &Ctx) {
  std::set<std::string> Pending;
  collectReferencedLogicFunctions(Module.CorrectnessGoal.get(), Pending);

  while (!Pending.empty()) {
    std::string Identity = *Pending.begin();
    Pending.erase(Pending.begin());
    if (Module.LogicFunctions.count(Identity))
      continue;

    const VFunction *Spec = findSpecFunction(Ctx.Functions, Identity);
    if (!Spec)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "missing spec definition: %s",
                                     Identity.c_str());

    LogicFunctionDecl Declaration;
    Declaration.Identity = Spec->Identity;
    Declaration.DisplayName = Spec->Name;
    Declaration.ResultSort = specLogicSort(Spec->ReturnType, Spec->IntMode);
    if (Declaration.ResultSort.Kind == LogicSortKind::Invalid)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "unsupported spec result type: %s",
                                     Spec->Name.c_str());
    for (const auto &[Name, Type] : Spec->Params) {
      LogicFunctionParameter Parameter;
      Parameter.Name = Name;
      Parameter.Sort = specLogicSort(Type, Spec->IntMode);
      if (Parameter.Sort.Kind == LogicSortKind::Invalid)
        return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                       "unsupported spec parameter type: %s",
                                       Spec->Name.c_str());
      Declaration.Parameters.push_back(std::move(Parameter));
    }

    auto [It, Inserted] =
        Module.LogicFunctions.try_emplace(Identity, std::move(Declaration));
    (void)Inserted;
    LogicFunctionDecl &Owned = It->second;

    unsigned Fuel = 0;
    if (Ctx.HiddenSpecs.count(Spec->Identity))
      Fuel = 0;
    else if (auto F = Ctx.SpecFuel.find(Spec->Identity);
             F != Ctx.SpecFuel.end())
      Fuel = F->second;
    else if (Ctx.RevealedSpecs.count(Spec->Identity))
      Fuel = 1;
    else
      Fuel = Spec->NeedsDecreasesCheck ? 1 : 64;

    const unsigned MaxDepth =
        Spec->NeedsDecreasesCheck ? Fuel : std::min(Fuel, 1U);
    Owned.DefinitionFuel = MaxDepth;
    for (unsigned Depth = 1; Depth <= MaxDepth; ++Depth) {
      std::unique_ptr<VExpr> Body = unfoldSpecDefinition(*Spec, Ctx, Depth);
      if (!Body)
        continue;
      auto Lowered = lowerLogicExpr(
          Body.get(), "", std::string(VHeapName) + "_0", Spec->IntMode);
      if (!Lowered)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "spec definition lowering failed for %s: %s", Spec->Name.c_str(),
            llvm::toString(Lowered.takeError()).c_str());
      std::unique_ptr<LogicExpr> Definition = coerceDefinition(
          std::move(*Lowered), Spec->ReturnType, Spec->IntMode);
      if (!Definition)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "spec definition result sort mismatch: %s", Spec->Name.c_str());
      collectReferencedLogicFunctions(Definition.get(), Pending);
      if (Depth == 1) {
        auto StepBody = unfoldSpecDefinition(*Spec, Ctx, /*Fuel=*/1);
        if (!StepBody)
          return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                         "spec step definition unavailable: %s",
                                         Spec->Name.c_str());
        auto StepLowered = lowerLogicExpr(
            StepBody.get(), "", std::string(VHeapName) + "_0", Spec->IntMode);
        if (!StepLowered)
          return llvm::createStringError(
              llvm::inconvertibleErrorCode(),
              "spec step definition lowering failed for %s: %s",
              Spec->Name.c_str(),
              llvm::toString(StepLowered.takeError()).c_str());
        Owned.StepDefinition = coerceDefinition(
            std::move(*StepLowered), Spec->ReturnType, Spec->IntMode);
        if (!Owned.StepDefinition)
          return llvm::createStringError(
              llvm::inconvertibleErrorCode(),
              "spec step definition result sort mismatch: %s",
              Spec->Name.c_str());
        collectReferencedLogicFunctions(Owned.StepDefinition.get(), Pending);
      }
      Owned.DefinitionLevels.push_back(std::move(Definition));
    }
  }
  return llvm::Error::success();
}