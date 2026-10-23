#include "ChildProcess.h"
#include "llvm/Support/ConvertUTF.h"
#include <system_error>

#if defined(_WIN32)
#include "llvm/Support/Windows/WindowsSupport.h"
#else
#include <cerrno>
#include <csignal>
#include <sys/wait.h>
#if defined(__APPLE__)
#include <crt_externs.h>
#define environ (*_NSGetEnviron())
#else
extern char **environ;
#endif
#endif

namespace clang {
namespace verify {

ChildPoll pollChild(const llvm::sys::ProcessInfo &Process,
                    llvm::StringRef Name) {
#if defined(_WIN32)
  std::string Error;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, 0, &Error, nullptr, true);
  if (Waited.Pid == llvm::sys::ProcessInfo::InvalidPid)
    return {ChildState::Running, -1, {}};
  if (Waited.Pid != Process.Pid)
    return {ChildState::Failed, -1,
            Error.empty() ? "cannot poll " + Name.str() + " process"
                          : std::move(Error)};
  return {ChildState::Exited, Waited.ReturnCode, std::move(Error)};
#else
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, WNOHANG);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == 0)
    return {};
  if (Waited == -1)
    return {ChildState::Failed, -1,
            "cannot poll " + Name.str() + " process: " +
                std::error_code(errno, std::generic_category()).message()};
  if (WIFEXITED(Status))
    return {ChildState::Exited, WEXITSTATUS(Status), {}};
  if (WIFSIGNALED(Status))
    return {ChildState::Exited, -2,
            Name.str() + " terminated by signal " +
                std::to_string(WTERMSIG(Status))};
  return {ChildState::Failed, -1,
          Name.str() + " changed to an unsupported process state"};
#endif
}

bool terminateChild(const llvm::sys::ProcessInfo &Process, llvm::StringRef Name,
                    std::string &Error) {
#if defined(_WIN32)
  if (!::TerminateProcess(static_cast<HANDLE>(Process.Process), 1) &&
      ::GetLastError() != ERROR_ACCESS_DENIED) {
    Error = "cannot terminate " + Name.str() + " process";
    return false;
  }
  std::string WaitError;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, std::nullopt, &WaitError);
  if (Waited.Pid != Process.Pid) {
    Error = WaitError.empty() ? "cannot reap " + Name.str() + " process"
                              : std::move(WaitError);
    return false;
  }
  return true;
#else
  if (::kill(Process.Pid, SIGKILL) == -1 && errno != ESRCH) {
    Error = "cannot terminate " + Name.str() + " process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, 0);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == -1 && errno != ECHILD) {
    Error = "cannot reap " + Name.str() + " process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  return true;
#endif
}

std::vector<std::string> childEnvironment(llvm::StringRef Variable,
                                          llvm::StringRef Value) {
  std::vector<std::string> Environment;
  auto add = [&](llvm::StringRef Entry) {
    if (!Entry.starts_with((Variable + "=").str()))
      Environment.push_back(Entry.str());
  };
#if defined(_WIN32)
  if (wchar_t *Block = ::GetEnvironmentStringsW()) {
    for (const wchar_t *Entry = Block; *Entry; Entry += wcslen(Entry) + 1) {
      std::string Narrow;
      if (llvm::convertWideToUTF8(Entry, Narrow))
        add(Narrow);
    }
    ::FreeEnvironmentStringsW(Block);
  }
#else
  for (char **Entry = environ; Entry && *Entry; ++Entry)
    add(*Entry);
#endif
  Environment.push_back((Variable + "=" + Value).str());
  return Environment;
}

} // namespace verify
} // namespace clang
