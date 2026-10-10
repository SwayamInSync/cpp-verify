//===--- Z3Encode.h - Obligation IR to Z3 -----------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "Certify.h"
#include "Obligation.h"
#include "ProofCache.h"
#include "VerifyBackend.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <functional>
#include <map>
#include <mutex>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>
#include <z3++.h>

namespace clang {
namespace verify {

class Z3CandidateModel;

class Z3Encoder {
  z3::context Ctx;
  z3::solver Solver;
  std::map<std::string, z3::expr> Vars;
  std::map<std::string, LogicSort> ModelVariables;
  std::map<std::string, const LogicFunctionDecl *> LogicFunctions;
  std::map<std::string, z3::func_decl> SpecFuncDecls;
  unsigned TimeoutMs = 0;
  bool ProfileQuantifiers = false;
  /// Rerun Assertions counting quantifier instantiations.
  std::vector<QuantifierProfileEntry>
  profileQuantifiers(const z3::expr_vector &Assertions);
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
  std::chrono::steady_clock::time_point QueryStart;
  std::optional<unsigned> CertifyTimeoutMs;
  bool QuantifiedQuery = false;
  z3::solver freshSolver();
  /// \p S.check() within \p Ms milliseconds (0: no limit), unknown at once
  /// after interrupt().
  z3::check_result check(z3::solver &S, unsigned Ms);
  /// A check outlived its time and was interrupted.
  bool Overran = false;
  std::mutex CheckLock;
  std::condition_variable CheckChanged;
  bool CheckFinished = true;
  bool Stopped = false;
  /// The encoder running a pass of this one's query, which an interrupt
  /// reaches too.
  Z3Encoder *Pass = nullptr;
  /// Runs \p Inner as a pass of this encoder while it lives.
  struct PassScope {
    Z3Encoder &Outer;
    PassScope(Z3Encoder &Outer, Z3Encoder &Inner);
    ~PassScope();
  };
  /// Index, membership, and split facts for sequences, and extensionality
  /// instances.
  bool SequenceFacts = true;
  /// Encode logical functions as native recursive definitions. Hidden ones
  /// are defined too, but only to find counterexamples: an unsat that may use
  /// them is not a proof.
  bool NativeRecursion = false;
  /// No domain probing or coverage, and refinement rounds of at most
  /// MaxProofRoundInstances, since thousands of ground instances can stall
  /// the solver: for a module solved as an attempt (ModuleAttempt).
  bool ProofOnly = false;
  std::set<std::string> NativeHidden;
  /// With NativeRecursion, non-recursive functions are replaced by their
  /// definitions: parameters and body, encoded once.
  std::set<std::string> NonRecursive;
  std::map<std::string, std::pair<z3::expr_vector, z3::expr>> Inlined;
  /// With NativeRecursion, each recursive definition with its recursion
  /// under case splits, or null when it cannot be: Z3 expands a definition
  /// with a single case at every application, without a depth bound.
  std::map<std::string, std::unique_ptr<LogicExpr>> NativeBodies;
  /// Whether \p Function is given to Z3 as a native recursive definition.
  bool nativelyDefined(const LogicFunctionDecl &Function);
  unsigned EncodingPass = 0;
  std::vector<const LogicFunctionDecl *> UndefinedRecursive;
  /// Refinement stopped on a bounded domain; native definitions may settle it.
  bool EscalateToNative = false;
  /// A bounded domain was found in the bit-vector encoding: the integer
  /// encoding, as exact, settles it much faster.
  bool CoverInIntegers = false;

  z3::sort intSort();
  z3::sort bvSort(unsigned BitWidth);
  z3::sort boolSort();
  z3::sort heapSort();
  z3::sort valueSort(const LogicSort &Sort);
  /// The option datatype of map cells: none, or some(value).
  z3::sort optionSort();
  std::optional<z3::sort> OptionSort;
  std::optional<z3::func_decl> NoneDecl, SomeDecl, IsSomeDecl, OptionValueDecl;
  z3::expr encodeCollection(const VCExpr *E, std::vector<z3::expr> Args);
  /// s[k] as the recursive-function definition cppverify.seq_at.
  z3::expr seqAt(const z3::expr &S, const z3::expr &K);
  std::optional<z3::func_decl> SeqAtDecl;
  /// Axioms of the collection functions the query uses, asserted beside it.
  std::vector<z3::expr> CollectionAxioms;
  /// forall k. Term[k] == Element(k), triggered by reads of Term: what each
  /// element of a sequence the query builds is. Quantified over the index
  /// only, so model search can check it and it fires only on terms of the
  /// query, never on the sequences Z3 creates while solving word equations.
  void indexFacts(const z3::expr &Term,
                  llvm::function_ref<z3::expr(const z3::expr &)> Element);
  /// forall Bound. Body, triggered by Trigger: a theorem stated beside the
  /// query, with an id starting "fact!" for --profile-quantifiers.
  z3::expr theorem(const z3::expr &Bound, const z3::expr &Trigger,
                   const z3::expr &Body, const char *Id);
  /// forall Bound. Body, without a pattern, named for --profile-quantifiers.
  z3::expr namedForall(const z3::expr &Bound, const z3::expr &Body,
                       const char *Id);
  std::set<unsigned> IndexedTerms;
  std::set<unsigned> SplitExtracts;
  /// Term, or a constant defined as the closed Term when Term contains an
  /// ite, which a pattern cannot.
  z3::expr patternable(const z3::expr &Term);
  std::map<unsigned, z3::expr> PatternNames;
  /// Relates seq.contains(S, unit(X)) to the reads of S, which Z3 does not.
  void bridgeContains(const z3::expr &Contains, const z3::expr &S,
                      const z3::expr &X);
  std::set<unsigned> BridgedContains;
  /// seq.extract(S, From, Count); an extract of a concatenation also gets
  /// the instance of the lemma that splits it.
  z3::expr seqExtract(const z3::expr &S, const z3::expr &From,
                      const z3::expr &Count);
  /// Equality of two collections of Sort: a multiset's counts.
  z3::expr collectionEquality(const LogicSort &Sort, const z3::expr &L,
                              const z3::expr &R);
  z3::expr heapVar(const std::string &Name);
  z3::expr asBool(z3::expr E);
  z3::expr fallbackValue(const VCExpr *E);
  z3::expr arithOp(const VCExpr *E, z3::expr L, z3::expr R);
  void markEncodingFailure(std::string Message);
  z3::func_decl specFuncDecl(const LogicFunctionDecl &Function);
  /// A trigger term as Z3 matches it: a raw heap select or an opaque
  /// function application; nullopt when it cannot be one.
  std::optional<z3::expr> patternTerm(const VCExpr *Term);
  /// A quantifier over Binders with E's trigger, named for profiling by its
  /// source position.
  z3::expr quantify(const VCExpr *E, bool Forall, z3::expr_vector &Binders,
                    const z3::expr &Body);
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

  z3::expr symbol(const std::string &Name, const LogicSort &Sort);
  z3::func_decl validPointerDecl();
  /// A literal term for a canonical value of Sort.
  z3::expr valueTerm(const LogicValue &Value, const LogicSort &Sort);
  /// A typed load in the integer encoding: the cell reduced into Sort. In a
  /// query over collections it is a recursive-function definition, so that
  /// a collection element read from a cell equals a load of that cell by
  /// congruence, without the reduction's mod under every quantifier
  /// instance. Elsewhere the reduction is inline: model search over heap
  /// frames is much faster with it.
  z3::expr cellValue(const z3::expr &Cell, const LogicSort &Sort);
  bool CellFunctions = false;
  /// Per context: each definition with its SMT-LIB text.
  std::map<std::string, std::pair<z3::func_decl, std::string>> CellDecls;
  std::set<std::string> UsedCellDecls;
  z3::expr arrayTerm(const HeapValue &Heap,
                     const std::function<z3::expr(const CertInt &)> &Cell);
  /// \p E's value in \p Model. An evaluation cut short (a race interrupts
  /// the context while its model is read) gives no term, which reads as an
  /// opaque constant: undetermined, never a value.
  z3::expr evaluated(const z3::model &Model, const z3::expr &E,
                     bool Completion);
  /// \p Limits within the time one check may take (--certify-timeout).
  CertifyLimits checkLimits(CertifyLimits Limits) const;
  /// The certifier's verdict on \p Candidate; undetermined once the encoder
  /// was stopped, since its model then evaluates unreliably.
  CertifyResult certify(const ObligationModule &Module, const LogicExpr &Query,
                        CandidateModel &Candidate, const CertifyLimits &Limits);
  std::optional<LogicValue> modelValue(const z3::model &Model,
                                       const z3::expr &Value,
                                       const LogicSort &Sort);
  /// An array model value read cell by cell between the numerals it
  /// mentions; Decode reads a cell (an integer by default).
  std::optional<HeapValue> piecewiseHeap(
      const z3::model &Model, const z3::expr &Value,
      const std::function<std::optional<CertInt>(const z3::expr &)> &Decode =
          nullptr);
  std::optional<HeapValue> heapValue(const z3::model &Model,
                                     const z3::expr &Value);
  /// f(args) = definition[args], true of the defined function.
  std::optional<z3::expr>
  definitionInstance(const DefinitionInstance &Instance);
  /// Keep a satisfying model only if the certifier confirms it; otherwise give
  /// the solver definition instances at the disputed applications and solve
  /// again. Sets \p Out to Unresolved when that does not settle it.
  z3::check_result certifyModels(const ObligationModule &Module,
                                 const LogicExpr &Query,
                                 z3::check_result Result, VerifyResult &Out);
  /// The disputes of models at the least and greatest values the solver
  /// allows for the integer arguments of disputed applications, when it proves
  /// those values bounded. Covering a bounded domain this way takes a few
  /// checks instead of one round per value. \p Pin is set instead when such a
  /// model is a real counterexample. The searches of the ends take turns until
  /// \p Until, each check with an equal share of the time left.
  std::vector<SpecDispute>
  boundedDomainDisputes(const ObligationModule &Module, const LogicExpr &Query,
                        const CertifyResult &Disputed, const z3::model &Model,
                        std::chrono::steady_clock::time_point Until,
                        std::optional<z3::expr> &Pin);
  friend class Z3CandidateModel;
  bool defineRecursiveFunctions();
  bool inlined(const LogicFunctionDecl &Function) const {
    return NonRecursive.count(Function.Identity);
  }
  /// \p Function's definition at \p Args.
  z3::expr inlineDefinition(const LogicFunctionDecl &Function,
                            const std::vector<z3::expr> &Args);
  /// \p Function's definition over fresh parameter constants.
  std::pair<z3::expr_vector, z3::expr>
  encodeDefinition(const LogicFunctionDecl &Function);
  std::optional<VerifyResult>
  verifyNatively(const ObligationModule &Module, const LogicExpr *Query,
                 std::optional<uint64_t> TraceEventCount,
                 VerifyResult &FuelResult);
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
  /// The time one counterexample check may take; unset, half the timeout;
  /// 0, the query's own time.
  void setCertifyTimeoutMs(std::optional<unsigned> Ms) {
    CertifyTimeoutMs = Ms;
  }
  /// Stops the check running in this encoder, from any thread.
  void interrupt();
  /// Lets checks run again after interrupt().
  void resume();
  /// Without SequenceFacts the query is in the solver's plain sequence
  /// theory, which finds models faster and proofs slower.
  void setSequenceFacts(bool Value) { SequenceFacts = Value; }
  void setProofOnly(bool Value) { ProofOnly = Value; }
  void setResourceLimit(unsigned Limit) { ResourceLimit = Limit; }
  void setIntegerEncoding(MachineIntegerEncoding Encoding) {
    IntegerEncoding = Encoding;
  }
  void setProfileQuantifiers(bool Profile) { ProfileQuantifiers = Profile; }
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
  /// The timeout of the module being verified.
  unsigned TimeoutMs;
  std::optional<unsigned> CertifyTimeoutMs;
  unsigned SolverTimeoutMs;
  std::optional<unsigned> CollectionTimeoutMs;
  unsigned ResourceLimit;
  unsigned Jobs;
  llvm::ThreadPoolInterface *Pool;
  uint64_t MaxQueryNodes;
  MachineIntegerEncoding IntegerEncoding;
  bool SkipWholeModuleRetry;
  bool SingleQuery;
  bool ProfileQuantifiers;
  std::unique_ptr<ProofCache> Cache;
  bool ReuseVerifiedQueries;
  std::set<std::string> VerifiedQueries;

  std::optional<std::chrono::steady_clock::time_point> Deadline;
  unsigned budget(unsigned Ms) const { return withinDeadline(Ms, Deadline); }
  /// The function's time is spent, so no further query starts.
  bool spent() const {
    return Cancellation.Cancelled ||
           (Deadline && std::chrono::steady_clock::now() >= *Deadline);
  }

  /// Strategies solving one module at once: whichever settles it first
  /// interrupts the others.
  struct Race {
    std::mutex Lock;
    std::atomic<bool> Cancelled{false};
    std::set<Z3Encoder *> Running;
    void enter(Z3Encoder &Encoder);
    void leave(Z3Encoder &Encoder);
    void cancel();
    /// Lets the encoders still entered run again.
    void reset();
  };
  /// Every encoder this backend runs, which cancel() stops.
  Race Cancellation;

  VerifyResult verifyModuleDirect(const ObligationModule &Module);
  /// Whether a query over \p Module is also solved without sequence facts.
  bool racesEncodings(const ObligationModule &Module) const;
  /// \p Query of \p Module (null: the complete query) in a fresh encoder,
  /// and, when racesEncodings, at once in one without sequence facts.
  VerifyResult solveQuery(const ObligationModule &Module,
                          const LogicExpr *Query,
                          std::optional<uint64_t> TraceEventCount,
                          unsigned Timeout, Race *Racing);
  VerifyResult verifyObligation(const ObligationModule &Module,
                                const Obligation &Item,
                                llvm::StringRef SemanticHash = {},
                                const ProofCacheLookup *Lookup = nullptr,
                                bool Reused = false, Race *Racing = nullptr);

public:
  explicit Z3VerifyBackend(const BackendExecutionOptions &Execution = {},
                           llvm::StringRef CacheBackendName = "z3",
                           bool ReuseVerifiedQueries = false);
  llvm::StringRef getName() const override { return "z3"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }
  /// One result per obligation in order. With StopAtFailure a serial run ends
  /// after the first failure, since later results cannot change it. A nonzero
  /// TimeoutCapMs bounds every query's timeout.
  std::vector<VerifyResult> verifyObligations(const ObligationModule &Module,
                                              bool StopAtFailure = false,
                                              Race *Racing = nullptr,
                                              unsigned TimeoutCapMs = 0);
  void cancel() override { Cancellation.cancel(); }
  void resume() override { Cancellation.reset(); }
  std::optional<unsigned>
  queryTimeoutMs(const ObligationModule &Module) const override {
    return moduleTimeoutMs(Module, SolverTimeoutMs, CollectionTimeoutMs);
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override;
  void applyDeadline(
      std::optional<std::chrono::steady_clock::time_point> D) override {
    Deadline = D;
  }
};

} // namespace verify
} // namespace clang

#endif