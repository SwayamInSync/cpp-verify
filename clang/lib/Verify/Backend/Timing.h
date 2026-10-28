//===--- Timing.h - Where a function's verification spends its time -----===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_TIMING_H
#define LLVM_CLANG_VERIFY_BACKEND_TIMING_H

#include <atomic>
#include <chrono>
#include <cstdint>

namespace clang {
namespace verify {

/// The time the backends of one function's verification spend, in
/// nanoseconds: solving is the wall time in VerifyBackend::verify, induction
/// the part of it spent on inductions, and certification the time of the
/// counterexample checks, summed over checks that may run at once.
struct BackendTimes {
  std::atomic<uint64_t> Solving{0};
  std::atomic<uint64_t> Induction{0};
  std::atomic<uint64_t> Certification{0};
};

/// Adds the time from its construction to its destruction to a counter, if
/// there is one.
class TimeInto {
  std::atomic<uint64_t> *Counter;
  std::chrono::steady_clock::time_point Start;

public:
  explicit TimeInto(std::atomic<uint64_t> *Counter)
      : Counter(Counter), Start(std::chrono::steady_clock::now()) {}
  TimeInto(const TimeInto &) = delete;
  TimeInto &operator=(const TimeInto &) = delete;
  ~TimeInto() {
    if (Counter)
      Counter->fetch_add(std::chrono::duration_cast<std::chrono::nanoseconds>(
                             std::chrono::steady_clock::now() - Start)
                             .count());
  }
};

} // namespace verify
} // namespace clang

#endif
