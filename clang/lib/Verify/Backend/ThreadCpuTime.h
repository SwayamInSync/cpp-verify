//===--- ThreadCpuTime.h - CPU time of one thread, read from any thread ---===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_THREADCPUTIME_H
#define LLVM_CLANG_VERIFY_BACKEND_THREADCPUTIME_H
#include <chrono>
#include <cstdint>
#include <optional>

namespace clang {
namespace verify {

/// The CPU time one thread has used: the work done on it, which the load of
/// other processes does not stretch as it stretches the wall clock. Another
/// thread may read it, as a check's watchdog does.
class ThreadCpuClock {
public:
  /// The clock of the calling thread.
  static ThreadCpuClock current();
  ThreadCpuClock(ThreadCpuClock &&Other);
  ThreadCpuClock(const ThreadCpuClock &) = delete;
  ThreadCpuClock &operator=(const ThreadCpuClock &) = delete;
  ThreadCpuClock &operator=(ThreadCpuClock &&) = delete;
  ~ThreadCpuClock();

  /// The CPU time the thread has used so far; none where the platform does
  /// not say.
  std::optional<std::chrono::microseconds> used() const;

private:
  ThreadCpuClock() = default;
  /// The platform's name for the thread or its clock.
  uintptr_t Handle = 0;
  bool Valid = false;
};

} // namespace verify
} // namespace clang

#endif
