//===- unittests/Verify/ThreadCpuTimeTest.cpp -----------------------------===//
//
// A thread's CPU clock counts the work done on that thread, read from it or
// from another thread, and not the time it waits.
//
//===----------------------------------------------------------------------===//

#include "Backend/ThreadCpuTime.h"
#include "gtest/gtest.h"
#include <atomic>
#include <chrono>
#include <thread>

using namespace clang::verify;

namespace {

using std::chrono::microseconds;
using std::chrono::milliseconds;

/// Works on the calling thread until \p Clock has counted \p Amount more,
/// or ten seconds pass; whether it got there.
bool work(const ThreadCpuClock &Clock, microseconds Amount) {
  const microseconds Start = *Clock.used();
  const auto Give = std::chrono::steady_clock::now() + std::chrono::seconds(10);
  volatile uint64_t Sink = 0;
  while (std::chrono::steady_clock::now() < Give) {
    for (unsigned I = 0; I != 100000; ++I)
      Sink = Sink + I;
    if (*Clock.used() - Start >= Amount)
      return true;
  }
  return false;
}

TEST(ThreadCpuTimeTest, CountsWorkNotWaiting) {
  const ThreadCpuClock Clock = ThreadCpuClock::current();
  if (!Clock.used())
    GTEST_SKIP() << "this platform does not read a thread's CPU time";
  EXPECT_TRUE(work(Clock, milliseconds(20)));
  const microseconds BeforeSleep = *Clock.used();
  std::this_thread::sleep_for(milliseconds(200));
  EXPECT_LT(*Clock.used() - BeforeSleep, milliseconds(100));
}

TEST(ThreadCpuTimeTest, ReadsAnotherThread) {
  const ThreadCpuClock Clock = ThreadCpuClock::current();
  if (!Clock.used())
    GTEST_SKIP() << "this platform does not read a thread's CPU time";
  // Another thread reads this one's clock while this one works, as a check's
  // watchdog does, and its own work does not count.
  std::atomic<bool> Done{false};
  microseconds SeenByOther{0};
  std::thread Other([&] {
    const microseconds Start = *Clock.used();
    volatile uint64_t Sink = 0;
    while (!Done)
      for (unsigned I = 0; I != 100000; ++I)
        Sink = Sink + I;
    SeenByOther = *Clock.used() - Start;
  });
  EXPECT_TRUE(work(Clock, milliseconds(30)));
  Done = true;
  Other.join();
  EXPECT_GE(SeenByOther, milliseconds(20));
}

TEST(ThreadCpuTimeTest, OtherThreadsDoNotCount) {
  const ThreadCpuClock Clock = ThreadCpuClock::current();
  if (!Clock.used())
    GTEST_SKIP() << "this platform does not read a thread's CPU time";
  const microseconds Start = *Clock.used();
  std::thread Busy([] {
    const ThreadCpuClock Own = ThreadCpuClock::current();
    EXPECT_TRUE(work(Own, milliseconds(50)));
  });
  Busy.join();
  EXPECT_LT(*Clock.used() - Start, milliseconds(25));
}

} // namespace
