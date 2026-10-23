//===--- ChildProcess.h - Polling and stopping a process ----------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_CHILDPROCESS_H
#define LLVM_CLANG_VERIFY_BACKEND_CHILDPROCESS_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Program.h"
#include <string>
#include <vector>

namespace clang {
namespace verify {

enum class ChildState { Running, Exited, Failed };

struct ChildPoll {
  ChildState State = ChildState::Running;
  int ExitCode = -1;
  std::string Error;
};

/// Whether the process has ended, without waiting for it. Name is what the
/// messages call it.
ChildPoll pollChild(const llvm::sys::ProcessInfo &Process,
                    llvm::StringRef Name);

/// Kills the process and reaps it.
bool terminateChild(const llvm::sys::ProcessInfo &Process, llvm::StringRef Name,
                    std::string &Error);

/// This process's environment with Variable set to Value, for a child: a
/// child of several started at once cannot be given it by changing ours.
std::vector<std::string> childEnvironment(llvm::StringRef Variable,
                                          llvm::StringRef Value);

} // namespace verify
} // namespace clang

#endif
