//===--- QueryDump.h - Solver queries as SMT-LIB scripts --------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_QUERYDUMP_H
#define LLVM_CLANG_VERIFY_BACKEND_QUERYDUMP_H

#include "Obligation.h"
#include "llvm/ADT/StringRef.h"
#include <string>

namespace clang {
namespace verify {

/// Writes every query sent to a solver under \p Directory, each as a script
/// the solver replays on its own (--dump-smt2); an empty directory turns it
/// off. \p Tool names the program in each script's header.
void setQueryDumpDirectory(std::string Directory, std::string Tool);

/// Whether queries are being written.
bool queryDumpEnabled();

/// The first error writing a query, empty when there was none.
std::string queryDumpError();

/// The file of \p Query of \p Module solved by \p Solver whose script is
/// \p Script, relative to the dump directory:
/// `<function>-<h6>/<query>.<solver>-<h8>.smt2`.
std::string queryDumpPath(const ObligationModule *Module,
                          const LogicExpr *Query, llvm::StringRef Solver,
                          llvm::StringRef Script);

/// One query's script: written when the dump starts, before the check, so
/// that a check that never returns leaves its query, and finished with the
/// solver's answer.
class QueryDump {
public:
  QueryDump() = default;
  QueryDump(const QueryDump &) = delete;
  QueryDump &operator=(const QueryDump &) = delete;

  /// Writes \p Options, the solver's settings as commands, then \p Script,
  /// which ends with its check, after a header that names \p Solver
  /// (\p SolverVersion) and what \p Query of \p Module is. Does nothing
  /// unless dumping is on.
  void start(const ObligationModule *Module, const LogicExpr *Query,
             llvm::StringRef Solver, llvm::StringRef SolverVersion,
             llvm::StringRef Options, llvm::StringRef Script);

  /// Appends \p Commands, run after the check (such as `(get-model)`), and
  /// the answer, `; cpp-verify: sat`.
  void finish(llvm::StringRef Answer, llvm::StringRef Commands = "");

private:
  std::string Path;
};

} // namespace verify
} // namespace clang

#endif
