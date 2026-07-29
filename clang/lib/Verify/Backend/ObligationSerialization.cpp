//===--- ObligationSerialization.cpp --------------------------------------===//
#include "ObligationSerialization.h"
#include "llvm/Support/SHA256.h"
#include <array>
#include <limits>
#include <optional>

using namespace clang;
using namespace verify;

namespace {

constexpr std::array<char, 8> ArchiveMagic = {'C', 'P', 'V',  'O',
                                              'B', 'L', '\r', '\n'};
constexpr uint32_t HasSourceMetadata = 1U << 0;
constexpr uint32_t HasBMCTransformProvenance = 1U << 1;
constexpr uint32_t HasSourceRanges = 1U << 2;
constexpr uint32_t HasDiagnosticMetadata = 1U << 3;
constexpr uint64_t MaxSerializedString = 64U * 1024U * 1024U;
constexpr uint64_t MaxSerializedCollection = 100000;
constexpr unsigned MaxExpressionDepth = 4096;
constexpr uint64_t MaxExpressionNodes = 100000;

void collectCalledFunctions(const LogicExpr *Expr,
                            std::set<std::string> &Called) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::SpecCall)
    Called.insert(Expr->SpecCallee);
  for (const auto &Child : Expr->Children)
    collectCalledFunctions(Child.get(), Called);
}

uint8_t sortTag(LogicSortKind Kind) {
  switch (Kind) {
  case LogicSortKind::Invalid:
    return 0;
  case LogicSortKind::Bool:
    return 1;
  case LogicSortKind::MathematicalInteger:
    return 2;
  case LogicSortKind::BitVector:
    return 3;
  case LogicSortKind::Pointer:
    return 4;
  case LogicSortKind::Heap:
    return 5;
  }
  llvm_unreachable("unknown logic sort");
}

std::optional<LogicSortKind> sortFromTag(uint8_t Tag) {
  switch (Tag) {
  case 0:
    return LogicSortKind::Invalid;
  case 1:
    return LogicSortKind::Bool;
  case 2:
    return LogicSortKind::MathematicalInteger;
  case 3:
    return LogicSortKind::BitVector;
  case 4:
    return LogicSortKind::Pointer;
  case 5:
    return LogicSortKind::Heap;
  default:
    return std::nullopt;
  }
}

uint8_t signednessTag(LogicSignedness Signedness) {
  switch (Signedness) {
  case LogicSignedness::None:
    return 0;
  case LogicSignedness::Signed:
    return 1;
  case LogicSignedness::Unsigned:
    return 2;
  }
  llvm_unreachable("unknown logic signedness");
}

std::optional<LogicSignedness> signednessFromTag(uint8_t Tag) {
  switch (Tag) {
  case 0:
    return LogicSignedness::None;
  case 1:
    return LogicSignedness::Signed;
  case 2:
    return LogicSignedness::Unsigned;
  default:
    return std::nullopt;
  }
}

uint8_t expressionTag(LogicExpr::Kind Kind) {
  switch (Kind) {
#define LOGIC_EXPR_TAG(Name, Tag)                                              \
  case LogicExpr::Name:                                                        \
    return Tag
    LOGIC_EXPR_TAG(True, 1);
    LOGIC_EXPR_TAG(False, 2);
    LOGIC_EXPR_TAG(IntLit, 3);
    LOGIC_EXPR_TAG(BoolLit, 4);
    LOGIC_EXPR_TAG(Var, 5);
    LOGIC_EXPR_TAG(Not, 6);
    LOGIC_EXPR_TAG(Neg, 7);
    LOGIC_EXPR_TAG(BitNot, 8);
    LOGIC_EXPR_TAG(Add, 9);
    LOGIC_EXPR_TAG(Sub, 10);
    LOGIC_EXPR_TAG(Mul, 11);
    LOGIC_EXPR_TAG(Div, 12);
    LOGIC_EXPR_TAG(Rem, 13);
    LOGIC_EXPR_TAG(BitAnd, 14);
    LOGIC_EXPR_TAG(BitOr, 15);
    LOGIC_EXPR_TAG(BitXor, 16);
    LOGIC_EXPR_TAG(Shl, 17);
    LOGIC_EXPR_TAG(Shr, 18);
    LOGIC_EXPR_TAG(Eq, 19);
    LOGIC_EXPR_TAG(Ne, 20);
    LOGIC_EXPR_TAG(Lt, 21);
    LOGIC_EXPR_TAG(Le, 22);
    LOGIC_EXPR_TAG(Gt, 23);
    LOGIC_EXPR_TAG(Ge, 24);
    LOGIC_EXPR_TAG(And, 25);
    LOGIC_EXPR_TAG(Or, 26);
    LOGIC_EXPR_TAG(Ite, 27);
    LOGIC_EXPR_TAG(ValidPtr, 28);
    LOGIC_EXPR_TAG(Select, 29);
    LOGIC_EXPR_TAG(Store, 30);
    LOGIC_EXPR_TAG(Forall, 31);
    LOGIC_EXPR_TAG(Exists, 32);
    LOGIC_EXPR_TAG(IntToBv, 33);
    LOGIC_EXPR_TAG(BvToInt, 34);
    LOGIC_EXPR_TAG(BvResize, 35);
    LOGIC_EXPR_TAG(NoOverflow, 36);
    LOGIC_EXPR_TAG(SpecCall, 37);
#undef LOGIC_EXPR_TAG
  }
  llvm_unreachable("unknown logic expression");
}

std::optional<LogicExpr::Kind> expressionFromTag(uint8_t Tag) {
  switch (Tag) {
#define LOGIC_EXPR_FROM_TAG(Name, Value)                                       \
  case Value:                                                                  \
    return LogicExpr::Name
    LOGIC_EXPR_FROM_TAG(True, 1);
    LOGIC_EXPR_FROM_TAG(False, 2);
    LOGIC_EXPR_FROM_TAG(IntLit, 3);
    LOGIC_EXPR_FROM_TAG(BoolLit, 4);
    LOGIC_EXPR_FROM_TAG(Var, 5);
    LOGIC_EXPR_FROM_TAG(Not, 6);
    LOGIC_EXPR_FROM_TAG(Neg, 7);
    LOGIC_EXPR_FROM_TAG(BitNot, 8);
    LOGIC_EXPR_FROM_TAG(Add, 9);
    LOGIC_EXPR_FROM_TAG(Sub, 10);
    LOGIC_EXPR_FROM_TAG(Mul, 11);
    LOGIC_EXPR_FROM_TAG(Div, 12);
    LOGIC_EXPR_FROM_TAG(Rem, 13);
    LOGIC_EXPR_FROM_TAG(BitAnd, 14);
    LOGIC_EXPR_FROM_TAG(BitOr, 15);
    LOGIC_EXPR_FROM_TAG(BitXor, 16);
    LOGIC_EXPR_FROM_TAG(Shl, 17);
    LOGIC_EXPR_FROM_TAG(Shr, 18);
    LOGIC_EXPR_FROM_TAG(Eq, 19);
    LOGIC_EXPR_FROM_TAG(Ne, 20);
    LOGIC_EXPR_FROM_TAG(Lt, 21);
    LOGIC_EXPR_FROM_TAG(Le, 22);
    LOGIC_EXPR_FROM_TAG(Gt, 23);
    LOGIC_EXPR_FROM_TAG(Ge, 24);
    LOGIC_EXPR_FROM_TAG(And, 25);
    LOGIC_EXPR_FROM_TAG(Or, 26);
    LOGIC_EXPR_FROM_TAG(Ite, 27);
    LOGIC_EXPR_FROM_TAG(ValidPtr, 28);
    LOGIC_EXPR_FROM_TAG(Select, 29);
    LOGIC_EXPR_FROM_TAG(Store, 30);
    LOGIC_EXPR_FROM_TAG(Forall, 31);
    LOGIC_EXPR_FROM_TAG(Exists, 32);
    LOGIC_EXPR_FROM_TAG(IntToBv, 33);
    LOGIC_EXPR_FROM_TAG(BvToInt, 34);
    LOGIC_EXPR_FROM_TAG(BvResize, 35);
    LOGIC_EXPR_FROM_TAG(NoOverflow, 36);
    LOGIC_EXPR_FROM_TAG(SpecCall, 37);
#undef LOGIC_EXPR_FROM_TAG
  default:
    return std::nullopt;
  }
}

uint8_t overflowTag(LogicOverflowOp Op) {
  switch (Op) {
  case LogicOverflowOp::Add:
    return 1;
  case LogicOverflowOp::Sub:
    return 2;
  case LogicOverflowOp::Mul:
    return 3;
  case LogicOverflowOp::Neg:
    return 4;
  case LogicOverflowOp::SignedDiv:
    return 5;
  }
  llvm_unreachable("unknown logic overflow operation");
}

std::optional<LogicOverflowOp> overflowFromTag(uint8_t Tag) {
  switch (Tag) {
  case 1:
    return LogicOverflowOp::Add;
  case 2:
    return LogicOverflowOp::Sub;
  case 3:
    return LogicOverflowOp::Mul;
  case 4:
    return LogicOverflowOp::Neg;
  case 5:
    return LogicOverflowOp::SignedDiv;
  default:
    return std::nullopt;
  }
}

uint8_t obligationTag(ObligationKind Kind) {
  switch (Kind) {
  case ObligationKind::Assertion:
    return 1;
  case ObligationKind::Postcondition:
    return 2;
  case ObligationKind::Unwinding:
    return 3;
  }
  llvm_unreachable("unknown obligation kind");
}

std::optional<ObligationKind> obligationFromTag(uint8_t Tag) {
  switch (Tag) {
  case 1:
    return ObligationKind::Assertion;
  case 2:
    return ObligationKind::Postcondition;
  case 3:
    return ObligationKind::Unwinding;
  default:
    return std::nullopt;
  }
}

uint8_t traceTag(DiagnosticTraceKind Kind) {
  switch (Kind) {
  case DiagnosticTraceKind::Branch:
    return 1;
  case DiagnosticTraceKind::Call:
    return 2;
  case DiagnosticTraceKind::Loop:
    return 3;
  case DiagnosticTraceKind::HeapWrite:
    return 4;
  case DiagnosticTraceKind::Allocation:
    return 5;
  case DiagnosticTraceKind::LifetimeEnd:
    return 6;
  case DiagnosticTraceKind::Deallocation:
    return 7;
  case DiagnosticTraceKind::Return:
    return 8;
  }
  llvm_unreachable("unknown diagnostic trace kind");
}

std::optional<DiagnosticTraceKind> traceFromTag(uint8_t Tag) {
  switch (Tag) {
  case 1:
    return DiagnosticTraceKind::Branch;
  case 2:
    return DiagnosticTraceKind::Call;
  case 3:
    return DiagnosticTraceKind::Loop;
  case 4:
    return DiagnosticTraceKind::HeapWrite;
  case 5:
    return DiagnosticTraceKind::Allocation;
  case 6:
    return DiagnosticTraceKind::LifetimeEnd;
  case 7:
    return DiagnosticTraceKind::Deallocation;
  case 8:
    return DiagnosticTraceKind::Return;
  default:
    return std::nullopt;
  }
}

class ArchiveWriter {
  std::string Data;
  bool IncludeSource;
  bool IncludeSourceRanges;
  bool IncludeDiagnostics;

public:
  explicit ArchiveWriter(bool IncludeSource)
      : IncludeSource(IncludeSource), IncludeSourceRanges(IncludeSource),
        IncludeDiagnostics(IncludeSource) {}

  void writeU8(uint8_t Value) { Data.push_back(static_cast<char>(Value)); }

  void writeU32(uint32_t Value) {
    for (unsigned Shift = 0; Shift != 32; Shift += 8)
      writeU8(static_cast<uint8_t>(Value >> Shift));
  }

  void writeU64(uint64_t Value) {
    for (unsigned Shift = 0; Shift != 64; Shift += 8)
      writeU8(static_cast<uint8_t>(Value >> Shift));
  }

  void writeBool(bool Value) { writeU8(Value ? 1 : 0); }

  void writeString(llvm::StringRef Value) {
    writeU64(Value.size());
    Data.append(Value.data(), Value.size());
  }

  void writeSort(const LogicSort &Sort) {
    writeU8(sortTag(Sort.Kind));
    writeU32(Sort.BitWidth);
    writeU8(signednessTag(Sort.Signedness));
  }

  void writeSource(const ObligationSource &Source) {
    if (!IncludeSource)
      return;
    writeString(Source.File);
    writeU32(Source.Line);
    writeU32(Source.Column);
    if (IncludeSourceRanges) {
      writeU32(Source.EndLine);
      writeU32(Source.EndColumn);
    }
  }

  void writeExpr(const LogicExpr *Expr) {
    writeBool(Expr != nullptr);
    if (!Expr)
      return;
    writeU8(expressionTag(Expr->K));
    writeSort(Expr->Sort);
    writeString(Expr->IntVal);
    writeBool(Expr->BoolVal);
    writeString(Expr->Name);
    writeString(Expr->Binder);
    writeU8(overflowTag(Expr->OverflowOp));
    writeString(Expr->SpecCallee);
    writeSource(Expr->Source);
    writeU64(Expr->Children.size());
    for (const auto &Child : Expr->Children)
      writeExpr(Child.get());
  }

  void writeFunction(const std::string &MapIdentity,
                     const LogicFunctionDecl &Function,
                     bool IncludeDisplayName) {
    writeString(MapIdentity);
    writeString(Function.Identity);
    writeString(IncludeDisplayName ? Function.DisplayName : "");
    writeU64(Function.Parameters.size());
    for (const LogicFunctionParameter &Parameter : Function.Parameters) {
      writeString(Parameter.Name);
      writeSort(Parameter.Sort);
    }
    writeSort(Function.ResultSort);
    writeU32(Function.DefinitionFuel);
    writeExpr(Function.StepDefinition.get());
    writeU64(Function.DefinitionLevels.size());
    for (const auto &Definition : Function.DefinitionLevels)
      writeExpr(Definition.get());
  }

  void writeFunctionSignature(const std::string &MapIdentity,
                              const LogicFunctionDecl &Function) {
    writeString(MapIdentity);
    writeString(Function.Identity);
    writeU64(Function.Parameters.size());
    for (const LogicFunctionParameter &Parameter : Function.Parameters)
      writeSort(Parameter.Sort);
    writeSort(Function.ResultSort);
  }

  void writeFunctions(const std::map<std::string, LogicFunctionDecl> &Functions,
                      bool IncludeDisplayNames) {
    writeU64(Functions.size());
    for (const auto &[Identity, Function] : Functions)
      writeFunction(Identity, Function, IncludeDisplayNames);
  }

  void writeModule(const ObligationModule &Module,
                   uint32_t FormatVersion = ObligationSerializationVersion) {
    Data.append(ArchiveMagic.data(), ArchiveMagic.size());
    writeU32(FormatVersion);
    uint32_t Flags = IncludeSource ? HasSourceMetadata : 0;
    if (Module.BMCTransform)
      Flags |= HasBMCTransformProvenance;
    if (IncludeSourceRanges)
      Flags |= HasSourceRanges;
    if (IncludeDiagnostics)
      Flags |= HasDiagnosticMetadata;
    writeU32(Flags);
    writeString(IncludeSource ? Module.FunctionName : "");
    writeString(Module.FunctionIdentity);
    writeU32(Module.RequiredFeatures);
    writeString(Module.ResultVarName);
    writeString(Module.HeapPrefix);
    if (Module.BMCTransform)
      writeU32(Module.BMCTransform->UnrollBound);
    if (IncludeDiagnostics) {
      writeU64(Module.DiagnosticVariables.size());
      for (const auto &[InternalName, Variable] : Module.DiagnosticVariables) {
        writeString(InternalName);
        writeString(Variable.DisplayName);
        writeSort(Variable.Sort);
        writeSource(Variable.Source);
      }
      writeU64(Module.TraceEvents.size());
      for (const DiagnosticTraceEvent &Event : Module.TraceEvents) {
        writeU8(traceTag(Event.Kind));
        writeString(Event.Message);
        writeSource(Event.Source);
        writeExpr(Event.Guard.get());
        writeU64(Event.Values.size());
        for (const DiagnosticTraceValue &Value : Event.Values) {
          writeString(Value.Label);
          writeExpr(Value.Value.get());
        }
      }
    }
    writeFunctions(Module.LogicFunctions, IncludeSource);
    writeExpr(Module.CorrectnessGoal.get());
    writeExpr(Module.CounterexampleQuery.get());
    writeU64(Module.Obligations.size());
    for (const Obligation &Item : Module.Obligations) {
      if (IncludeDiagnostics)
        writeString(Item.Id);
      if (IncludeDiagnostics)
        writeString(Item.StableId);
      if (IncludeDiagnostics)
        writeU64(Item.TraceEventCount);
      writeU8(obligationTag(Item.Kind));
      writeSource(Item.Source);
      writeExpr(Item.Goal.get());
      writeExpr(Item.CounterexampleQuery.get());
    }
  }

  void writeObligationSemantics(const ObligationModule &Module,
                                const Obligation &Item) {
    writeString("cppverify-obligation-semantic");
    writeU32(ObligationSemanticHashVersion);
    writeString(Module.FunctionIdentity);
    writeString(Module.ResultVarName);
    writeString(Module.HeapPrefix);
    if (Module.BMCTransform) {
      writeString("bmc-unroll");
      writeU32(Module.BMCTransform->UnrollBound);
    }
    std::set<std::string> Reachable;
    collectCalledFunctions(Item.Goal.get(), Reachable);
    collectCalledFunctions(Item.CounterexampleQuery.get(), Reachable);
    std::vector<std::string> Pending(Reachable.begin(), Reachable.end());
    for (unsigned I = 0; I != Pending.size(); ++I) {
      auto Function = Module.LogicFunctions.find(Pending[I]);
      if (Function == Module.LogicFunctions.end())
        continue;
      std::set<std::string> Dependencies;
      collectCalledFunctions(Function->second.StepDefinition.get(),
                             Dependencies);
      for (const auto &Definition : Function->second.DefinitionLevels)
        collectCalledFunctions(Definition.get(), Dependencies);
      for (const std::string &Dependency : Dependencies)
        if (Reachable.insert(Dependency).second)
          Pending.push_back(Dependency);
    }
    uint64_t FunctionCount = 0;
    for (const std::string &Identity : Reachable)
      FunctionCount += Module.LogicFunctions.count(Identity);
    writeU64(FunctionCount);
    for (const std::string &Identity : Reachable) {
      auto Function = Module.LogicFunctions.find(Identity);
      if (Function != Module.LogicFunctions.end())
        writeFunction(Identity, Function->second, false);
    }
    writeU8(obligationTag(Item.Kind));
    writeExpr(Item.Goal.get());
    writeExpr(Item.CounterexampleQuery.get());
  }

  std::string take() { return std::move(Data); }
};

class ArchiveReader {
  llvm::StringRef Data;
  uint64_t Offset = 0;
  uint64_t ExpressionNodes = 0;
  uint64_t ExpressionEdges = 0;
  bool IncludeSource = false;
  bool IncludeSourceRanges = false;
  bool IncludeDiagnostics = false;
  std::string Failure;
  std::map<std::string, std::string> FunctionSignatures;

  void fail(llvm::StringRef Message) {
    if (Failure.empty())
      Failure = Message.str();
  }

  bool has(uint64_t Size) const {
    return Size <= Data.size() && Offset <= Data.size() - Size;
  }

  uint8_t readU8() {
    if (!has(1)) {
      fail("truncated obligation archive");
      return 0;
    }
    return static_cast<uint8_t>(Data[Offset++]);
  }

  uint32_t readU32() {
    uint32_t Value = 0;
    for (unsigned Shift = 0; Shift != 32; Shift += 8)
      Value |= static_cast<uint32_t>(readU8()) << Shift;
    return Value;
  }

  uint64_t readU64() {
    uint64_t Value = 0;
    for (unsigned Shift = 0; Shift != 64; Shift += 8)
      Value |= static_cast<uint64_t>(readU8()) << Shift;
    return Value;
  }

  bool readBool() {
    uint8_t Value = readU8();
    if (Value > 1)
      fail("invalid boolean in obligation archive");
    return Value != 0;
  }

  std::string readString() {
    uint64_t Size = readU64();
    if (!Failure.empty())
      return {};
    if (Size > MaxSerializedString) {
      fail("oversized string in obligation archive");
      return {};
    }
    if (!has(Size)) {
      fail("truncated string in obligation archive");
      return {};
    }
    llvm::StringRef Value = Data.substr(Offset, Size);
    Offset += Size;
    if (Value.contains('\0'))
      fail("embedded NUL in obligation archive string");
    return Value.str();
  }

  uint64_t readCount() {
    uint64_t Count = readU64();
    if (!Failure.empty())
      return 0;
    if (Count > MaxSerializedCollection) {
      fail("oversized collection in obligation archive");
      return 0;
    }
    return Count;
  }

  LogicSort readSort() {
    std::optional<LogicSortKind> Kind = sortFromTag(readU8());
    if (!Kind)
      fail("invalid logic sort in obligation archive");
    LogicSort Sort{Kind.value_or(LogicSortKind::Invalid), readU32(),
                   LogicSignedness::None};
    std::optional<LogicSignedness> Signedness = signednessFromTag(readU8());
    if (!Signedness)
      fail("invalid signedness in obligation archive");
    Sort.Signedness = Signedness.value_or(LogicSignedness::None);
    if (Sort.Kind != LogicSortKind::BitVector &&
        Sort.Kind != LogicSortKind::MathematicalInteger && Sort.BitWidth != 0)
      fail("non-integer sort has a width in obligation archive");
    if ((Sort.Kind == LogicSortKind::BitVector ||
         Sort.Kind == LogicSortKind::MathematicalInteger) &&
        Sort.BitWidth == 0)
      fail("integer sort has no width in obligation archive");
    const bool Numeric = Sort.Kind == LogicSortKind::MathematicalInteger ||
                         Sort.Kind == LogicSortKind::BitVector ||
                         Sort.Kind == LogicSortKind::Pointer;
    if (Numeric != (Sort.Signedness != LogicSignedness::None))
      fail("logic sort has inconsistent signedness in obligation archive");
    return Sort;
  }

  ObligationSource readSource(bool IncludeSource) {
    if (!IncludeSource)
      return {};
    ObligationSource Source;
    Source.File = readString();
    Source.Line = readU32();
    Source.Column = readU32();
    if (IncludeSourceRanges) {
      Source.EndLine = readU32();
      Source.EndColumn = readU32();
    }
    return Source;
  }

  std::unique_ptr<LogicExpr> readExpr(unsigned Depth = 0) {
    if (!Failure.empty())
      return nullptr;
    bool Present = readBool();
    if (!Failure.empty() || !Present)
      return nullptr;
    if (Depth > MaxExpressionDepth || ++ExpressionNodes > MaxExpressionNodes) {
      fail("expression limit exceeded in obligation archive");
      return nullptr;
    }

    std::optional<LogicExpr::Kind> Kind = expressionFromTag(readU8());
    if (!Kind)
      fail("invalid expression kind in obligation archive");
    auto Expr = std::make_unique<LogicExpr>(Kind.value_or(LogicExpr::False));
    Expr->Sort = readSort();
    Expr->IntVal = readString();
    Expr->BoolVal = readBool();
    Expr->Name = readString();
    Expr->Binder = readString();

    std::optional<LogicOverflowOp> OverflowOp = overflowFromTag(readU8());
    if (!OverflowOp)
      fail("invalid overflow operation in obligation archive");
    Expr->OverflowOp = OverflowOp.value_or(LogicOverflowOp::Add);
    Expr->SpecCallee = readString();
    Expr->Source = readSource(IncludeSource);

    uint64_t Children = readCount();
    if (!Failure.empty())
      return Expr;
    if (Children > MaxExpressionNodes - ExpressionEdges) {
      fail("expression edge limit exceeded in obligation archive");
      return Expr;
    }
    ExpressionEdges += Children;
    Expr->Children.reserve(Children);
    for (uint64_t I = 0; I != Children && Failure.empty(); ++I)
      Expr->Children.push_back(readExpr(Depth + 1));
    return Expr;
  }

  LogicFunctionDecl readFunction() {
    LogicFunctionDecl Function;
    Function.Identity = readString();
    Function.DisplayName = readString();

    uint64_t Parameters = readCount();
    Function.Parameters.reserve(Parameters);
    for (uint64_t I = 0; I != Parameters && Failure.empty(); ++I) {
      LogicFunctionParameter Parameter;
      Parameter.Name = readString();
      Parameter.Sort = readSort();
      Function.Parameters.push_back(std::move(Parameter));
    }
    Function.ResultSort = readSort();
    Function.DefinitionFuel = readU32();
    Function.StepDefinition = readExpr();
    uint64_t Levels = readCount();
    Function.DefinitionLevels.reserve(Levels);
    for (uint64_t I = 0; I != Levels && Failure.empty(); ++I)
      Function.DefinitionLevels.push_back(readExpr());
    return Function;
  }

  ObligationModule readModule() {
    for (char Expected : ArchiveMagic)
      if (readU8() != static_cast<uint8_t>(Expected))
        fail("invalid obligation archive magic");
    uint32_t Version = readU32();
    if (Version != ObligationSerializationVersion)
      fail("unsupported obligation archive version");
    uint32_t Flags = readU32();
    if (Flags & ~(HasSourceMetadata | HasBMCTransformProvenance |
                  HasSourceRanges | HasDiagnosticMetadata))
      fail("unsupported obligation archive flags");
    IncludeSource = Flags & HasSourceMetadata;
    IncludeSourceRanges = Flags & HasSourceRanges;
    IncludeDiagnostics = Flags & HasDiagnosticMetadata;
    if ((IncludeSourceRanges || IncludeDiagnostics) && !IncludeSource)
      fail("diagnostic obligation metadata requires source metadata");

    ObligationModule Module;
    Module.FunctionName = readString();
    Module.FunctionIdentity = readString();
    Module.RequiredFeatures = readU32();
    Module.ResultVarName = readString();
    Module.HeapPrefix = readString();
    if (Flags & HasBMCTransformProvenance)
      Module.BMCTransform = BMCTransformProvenance{readU32()};
    if (IncludeDiagnostics) {
      uint64_t Variables = readCount();
      for (uint64_t I = 0; I != Variables && Failure.empty(); ++I) {
        std::string InternalName = readString();
        DiagnosticVariable Variable;
        Variable.DisplayName = readString();
        Variable.Sort = readSort();
        Variable.Source = readSource(IncludeSource);
        if (!Module.DiagnosticVariables
                 .emplace(std::move(InternalName), std::move(Variable))
                 .second)
          fail("duplicate diagnostic variable in obligation archive");
      }
      uint64_t TraceEvents = readCount();
      Module.TraceEvents.reserve(TraceEvents);
      for (uint64_t I = 0; I != TraceEvents && Failure.empty(); ++I) {
        DiagnosticTraceEvent Event;
        std::optional<DiagnosticTraceKind> Kind = traceFromTag(readU8());
        if (!Kind)
          fail("invalid diagnostic trace kind in obligation archive");
        Event.Kind = Kind.value_or(DiagnosticTraceKind::Branch);
        Event.Message = readString();
        Event.Source = readSource(IncludeSource);
        Event.Guard = readExpr();
        uint64_t Values = readCount();
        Event.Values.reserve(Values);
        for (uint64_t J = 0; J != Values && Failure.empty(); ++J) {
          DiagnosticTraceValue Value;
          Value.Label = readString();
          Value.Value = readExpr();
          Event.Values.push_back(std::move(Value));
        }
        Module.TraceEvents.push_back(std::move(Event));
      }
    }

    uint64_t Functions = readCount();
    for (uint64_t I = 0; I != Functions && Failure.empty(); ++I) {
      std::string MapIdentity = readString();
      LogicFunctionDecl Function = readFunction();
      if (!Module.LogicFunctions
               .emplace(std::move(MapIdentity), std::move(Function))
               .second)
        fail("duplicate logical function in obligation archive");
    }

    Module.CorrectnessGoal = readExpr();
    Module.CounterexampleQuery = readExpr();
    uint64_t Obligations = readCount();
    Module.Obligations.reserve(Obligations);
    for (uint64_t I = 0; I != Obligations && Failure.empty(); ++I) {
      Obligation Item;
      Item.Id = readString();
      if (IncludeDiagnostics)
        Item.StableId = readString();
      if (IncludeDiagnostics)
        Item.TraceEventCount = readU64();
      std::optional<ObligationKind> Kind = obligationFromTag(readU8());
      if (!Kind)
        fail("invalid obligation kind in obligation archive");
      Item.Kind = Kind.value_or(ObligationKind::Assertion);
      Item.Source = readSource(IncludeSource);
      Item.Goal = readExpr();
      Item.CounterexampleQuery = readExpr();
      Module.Obligations.push_back(std::move(Item));
    }
    return Module;
  }

public:
  explicit ArchiveReader(llvm::StringRef Data) : Data(Data) {}

  llvm::Expected<std::vector<ObligationModule>> readAll() {
    std::vector<ObligationModule> Modules;
    while (Offset != Data.size()) {
      ExpressionNodes = 0;
      ExpressionEdges = 0;
      ObligationModule Module = readModule();
      if (!Failure.empty())
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       Failure.c_str());
      LogicFeatureSet DeclaredFeatures = Module.RequiredFeatures;
      auto RequiredFeatures = validateObligationModule(Module);
      if (!RequiredFeatures)
        return RequiredFeatures.takeError();
      if (*RequiredFeatures != DeclaredFeatures)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "obligation archive feature declaration does not match contents");
      for (const auto &[Identity, Function] : Module.LogicFunctions) {
        ArchiveWriter Writer(false);
        Writer.writeFunctionSignature(Identity, Function);
        std::string Signature = Writer.take();
        auto Existing = FunctionSignatures.find(Identity);
        if (Existing != FunctionSignatures.end() &&
            Existing->second != Signature)
          return llvm::createStringError(
              llvm::inconvertibleErrorCode(),
              "conflicting logical function signatures across obligation "
              "archive records");
        if (Existing == FunctionSignatures.end())
          FunctionSignatures.emplace(Identity, std::move(Signature));
      }
      Modules.push_back(std::move(Module));
    }
    if (Modules.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "empty obligation archive");
    return Modules;
  }
};

std::string sha256(llvm::StringRef Data) {
  llvm::SHA256 Hasher;
  Hasher.update(Data);
  std::array<uint8_t, 32> Digest = Hasher.final();
  static constexpr char Hex[] = "0123456789abcdef";
  std::string Result;
  Result.reserve(64);
  for (uint8_t Byte : Digest) {
    Result.push_back(Hex[Byte >> 4]);
    Result.push_back(Hex[Byte & 0xf]);
  }
  return Result;
}

} // namespace

std::string verify::serializeObligationModule(const ObligationModule &Module) {
  ArchiveWriter Writer(true);
  Writer.writeModule(Module);
  return Writer.take();
}

llvm::Expected<std::vector<ObligationModule>>
verify::deserializeObligationModules(llvm::StringRef Archive) {
  return ArchiveReader(Archive).readAll();
}

std::string verify::obligationSemanticHash(const ObligationModule &Module) {
  ArchiveWriter Writer(false);
  Writer.writeModule(Module, ObligationSemanticHashVersion);
  return sha256(Writer.take());
}

std::string verify::obligationSemanticHash(const ObligationModule &Module,
                                           const Obligation &Item) {
  ArchiveWriter Writer(false);
  Writer.writeObligationSemantics(Module, Item);
  return sha256(Writer.take());
}
