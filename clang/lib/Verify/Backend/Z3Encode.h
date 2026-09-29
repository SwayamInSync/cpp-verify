//===--- Z3Encode.h - Obligation IR to Z3 -----------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "Obligation.h"
#include "ProofCache.h"
#include "VerifyBackend.h"
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>
#include <z3++.h>

namespace clang {
namespace verify {

class Z3Encoder {
  z3::context Ctx;
  z3::solver Solver;
  std::map<std::string, z3::expr> Vars;
  std::map<std::string, LogicSort> ModelVariables;
  std::map<std::string, const LogicFunctionDecl *> LogicFunctions;
  std::map<std::string, z3::func_decl> SpecFuncDecls;
  unsigned TimeoutMs = 0;
  unsigned ResourceLimit = 0;
  /// The requested encoding; Auto is resolved per query into ActiveEncoding.
  MachineIntegerEncoding IntegerEncoding = MachineIntegerEncoding::Auto;
  MachineIntegerEncoding ActiveEncoding = MachineIntegerEncoding::Integer;
  /// Integer-encoded variables; each gets a range fact beside the goal.
  std::map<std::string, LogicSort> MachineVariables;
  /// Quantifier binder names of the query and its logical definitions.
  std::set<std::string> BinderNames;
  /// Bit-vector names of integer terms by term, width, and signedness.
  std::map<std::tuple<unsigned, unsigned, bool>, z3::expr> BitShadows;
  std::vector<z3::expr> BitDefinitions;
  bool DefineBitShadows = false;
  /// Set when a non-constant operand's bits are needed; Auto then switches.
  bool UsedBitLevelOperation = false;
  bool EncodingFailed = false;
  std::string EncodingError;

  z3::sort intSort();
  z3::sort bvSort(unsigned BitWidth);
  z3::sort boolSort();
  z3::sort heapSort();
  z3::sort valueSort(const LogicSort &Sort);
  z3::expr heapVar(const std::string &Name);
  z3::expr asBool(z3::expr E);
  z3::expr fallbackValue(const VCExpr *E);
  z3::expr arithOp(const VCExpr *E, z3::expr L, z3::expr R);
  void markEncodingFailure(std::string Message);
  z3::func_decl specFuncDecl(const LogicFunctionDecl &Function);
  z3::expr encodeVCNode(const VCExpr *E,
                        const std::map<const VCExpr *, z3::expr> &Done);
  z3::expr encodeVC(const VCExpr *E);
  std::optional<z3::expr> encodeModule(const ObligationModule &Module,
                                       const LogicExpr *Query,
                                       VerifyResult &Result);
  std::optional<z3::expr> encodeModuleAs(const ObligationModule &Module,
                                         const LogicExpr *Query,
                                         VerifyResult &Result);
  z3::expr_vector rangeFacts();

  /// Model values for free symbols and the true definition of every defined
  /// logical function, for checking a counterexample.
  struct SpecTruth;
  std::optional<z3::expr> evalTrue(SpecTruth &Truth, const z3::expr &E);
  std::optional<z3::expr> evalQuantifier(SpecTruth &Truth, const z3::expr &Q);
  std::optional<z3::expr> applyTrue(SpecTruth &Truth,
                                    const LogicFunctionDecl &Function,
                                    const z3::expr_vector &Args);
  /// Keep a satisfying model only if it is a counterexample under the true
  /// definitions; otherwise add the definitions at the disputed points and
  /// solve again. Sets \p Out to Unresolved when that does not settle it.
  z3::check_result refineSpecModel(const ObligationModule &Module,
                                   const z3::expr &Semantics,
                                   z3::check_result Result, VerifyResult &Out);
  z3::expr coerceToSort(z3::expr E, const LogicSort &Target, bool IsSigned);
  void emitSpecCallAxiom(const VCExpr *Call);

  bool integerMode() const {
    return ActiveEncoding == MachineIntegerEncoding::Integer;
  }
  z3::expr coerce(z3::expr E, const LogicSort &Source, const LogicSort &Target,
                  bool IsSigned);
  z3::expr powerOfTwo(unsigned Exponent);
  z3::expr machineLiteral(llvm::StringRef Decimal, const LogicSort &Sort);
  z3::expr reduce(z3::expr Value, const LogicSort &Sort);
  z3::expr inRange(z3::expr Value, const LogicSort &Sort);
  z3::expr reinterpret(z3::expr Value, unsigned BitWidth, bool FromSigned,
                       bool ToSigned);
  z3::expr convertMachine(z3::expr Value, const LogicSort &Source,
                          const LogicSort &Target);
  z3::expr heapCell(z3::expr Value, const LogicSort &Sort);
  z3::expr machineBits(z3::expr Value, const LogicSort &Sort);
  bool mentionsBinder(const z3::expr &Root);
  z3::expr integerArithOp(const VCExpr *E, z3::expr L, z3::expr R);
  z3::expr integerNoOverflow(const VCExpr *E, std::vector<z3::expr> Operands);

public:
  Z3Encoder();
  void setTimeoutMs(unsigned Ms) { TimeoutMs = Ms; }
  void setResourceLimit(unsigned Limit) { ResourceLimit = Limit; }
  void setIntegerEncoding(MachineIntegerEncoding Encoding) {
    IntegerEncoding = Encoding;
  }
  /// The encoding the most recently encoded query actually used.
  MachineIntegerEncoding activeIntegerEncoding() const {
    return ActiveEncoding;
  }
  VerifyResult
  verifyModule(const ObligationModule &Module, const LogicExpr *Query = nullptr,
               std::optional<uint64_t> TraceEventCount = std::nullopt);
  VerifyResult lowerModule(const ObligationModule &Module,
                           llvm::raw_ostream *OS = nullptr);
};

class Z3VerifyBackend : public VerifyBackend {
  Z3Encoder Enc;
  unsigned TimeoutMs;
  unsigned ResourceLimit;
  unsigned Jobs;
  uint64_t MaxQueryNodes;
  MachineIntegerEncoding IntegerEncoding;
  bool SkipWholeModuleRetry;
  std::unique_ptr<ProofCache> Cache;
  bool ReuseVerifiedQueries;
  std::set<std::string> VerifiedQueries;

  VerifyResult verifyObligation(const ObligationModule &Module,
                                const Obligation &Item,
                                llvm::StringRef SemanticHash = {},
                                const ProofCacheLookup *Lookup = nullptr,
                                bool Reused = false);

public:
  explicit Z3VerifyBackend(const BackendExecutionOptions &Execution = {},
                           llvm::StringRef CacheBackendName = "z3",
                           bool ReuseVerifiedQueries = false);
  llvm::StringRef getName() const override { return "z3"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }
  /// One result per obligation in order. With StopAtFailure a serial run ends
  /// after the first failure, since later results cannot change it.
  std::vector<VerifyResult> verifyObligations(const ObligationModule &Module,
                                              bool StopAtFailure = false);

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override;
};

} // namespace verify
} // namespace clang

#endif