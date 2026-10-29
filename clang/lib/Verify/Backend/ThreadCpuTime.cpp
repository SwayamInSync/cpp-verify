//===--- ThreadCpuTime.cpp - CPU time of one thread, read from any thread -===//
#include "ThreadCpuTime.h"

#if defined(_WIN32)
#include "llvm/Support/Windows/WindowsSupport.h"
#elif defined(__APPLE__)
#include <mach/mach.h>
#include <pthread.h>
#else
#include <pthread.h>
#include <time.h>
#endif

using namespace clang::verify;

ThreadCpuClock ThreadCpuClock::current() {
  ThreadCpuClock Clock;
#if defined(_WIN32)
  // GetCurrentThread() names whichever thread uses it; a duplicate names
  // this one wherever it is read.
  HANDLE Thread = nullptr;
  Clock.Valid = DuplicateHandle(GetCurrentProcess(), GetCurrentThread(),
                                GetCurrentProcess(), &Thread,
                                THREAD_QUERY_LIMITED_INFORMATION, FALSE, 0);
  Clock.Handle = reinterpret_cast<uintptr_t>(Thread);
#elif defined(__APPLE__)
  // pthread_mach_thread_np does not take a reference to the port.
  Clock.Handle = pthread_mach_thread_np(pthread_self());
  Clock.Valid = Clock.Handle != MACH_PORT_NULL;
#else
  clockid_t Id;
  Clock.Valid = pthread_getcpuclockid(pthread_self(), &Id) == 0;
  Clock.Handle = static_cast<uintptr_t>(Id);
#endif
  return Clock;
}

ThreadCpuClock::ThreadCpuClock(ThreadCpuClock &&Other)
    : Handle(Other.Handle), Valid(Other.Valid) {
  Other.Valid = false;
}

ThreadCpuClock::~ThreadCpuClock() {
#if defined(_WIN32)
  if (Valid)
    CloseHandle(reinterpret_cast<HANDLE>(Handle));
#endif
}

std::optional<std::chrono::microseconds> ThreadCpuClock::used() const {
  if (!Valid)
    return std::nullopt;
#if defined(_WIN32)
  FILETIME Creation, Exit, Kernel, User;
  if (!GetThreadTimes(reinterpret_cast<HANDLE>(Handle), &Creation, &Exit,
                      &Kernel, &User))
    return std::nullopt;
  auto Ticks = [](const FILETIME &Time) {
    return (static_cast<uint64_t>(Time.dwHighDateTime) << 32) |
           Time.dwLowDateTime;
  };
  // FILETIME counts 100-nanosecond intervals.
  return std::chrono::microseconds((Ticks(Kernel) + Ticks(User)) / 10);
#elif defined(__APPLE__)
  thread_basic_info_data_t Info;
  mach_msg_type_number_t Count = THREAD_BASIC_INFO_COUNT;
  if (thread_info(static_cast<mach_port_t>(Handle), THREAD_BASIC_INFO,
                  reinterpret_cast<thread_info_t>(&Info),
                  &Count) != KERN_SUCCESS)
    return std::nullopt;
  return std::chrono::seconds(Info.user_time.seconds +
                              Info.system_time.seconds) +
         std::chrono::microseconds(Info.user_time.microseconds +
                                   Info.system_time.microseconds);
#else
  struct timespec Time;
  if (clock_gettime(static_cast<clockid_t>(Handle), &Time) != 0)
    return std::nullopt;
  return std::chrono::duration_cast<std::chrono::microseconds>(
      std::chrono::seconds(Time.tv_sec) +
      std::chrono::nanoseconds(Time.tv_nsec));
#endif
}
