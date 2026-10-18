//===--- TaskGroup.h - Tasks whose waiter runs only them -------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_TASKGROUP_H
#define LLVM_CLANG_VERIFY_BACKEND_TASKGROUP_H

#include "llvm/ADT/FunctionExtras.h"
#include "llvm/Support/ThreadPool.h"
#include <condition_variable>
#include <deque>
#include <future>
#include <memory>
#include <mutex>
#include <type_traits>
#include <utility>

namespace clang {
namespace verify {

/// Tasks run on a thread pool. A worker of the pool that waits for them runs
/// those not yet started, and then waits only for those running, so nesting
/// never exceeds the pool's workers. llvm::ThreadPoolTaskGroup's wait runs
/// whatever task the pool has next instead: a function whose own queries
/// were done ran another function's query in its wait, and its later checks
/// then found its time spent.
class TaskGroup {
public:
  explicit TaskGroup(llvm::StdThreadPool &Pool) : Pool(Pool) {}
  TaskGroup(const TaskGroup &) = delete;
  TaskGroup &operator=(const TaskGroup &) = delete;
  ~TaskGroup() { wait(); }

  template <typename Function>
  std::shared_future<std::invoke_result_t<Function &>> async(Function &&F) {
    using Result = std::invoke_result_t<Function &>;
    auto Promise = std::make_shared<std::promise<Result>>();
    std::shared_future<Result> Future = Promise->get_future().share();
    {
      std::lock_guard<std::mutex> Guard(S->Lock);
      S->Pending.push_back(
          [Promise, F = std::forward<Function>(F)]() mutable {
            if constexpr (std::is_void_v<Result>) {
              F();
              Promise->set_value();
            } else {
              Promise->set_value(F());
            }
          });
    }
    // A task queued after its group is done finds nothing to run.
    (void)Pool.async([S = S] {
      while (runNext(*S))
        ;
    });
    return Future;
  }

  void wait() {
    if (Pool.isWorkerThread())
      while (runNext(*S))
        ;
    std::unique_lock<std::mutex> Guard(S->Lock);
    S->Changed.wait(Guard,
                    [&] { return S->Pending.empty() && S->Running == 0; });
  }

private:
  struct State {
    std::mutex Lock;
    std::condition_variable Changed;
    std::deque<llvm::unique_function<void()>> Pending;
    unsigned Running = 0;
  };

  static bool runNext(State &S) {
    {
      llvm::unique_function<void()> Task;
      {
        std::lock_guard<std::mutex> Guard(S.Lock);
        if (S.Pending.empty())
          return false;
        Task = std::move(S.Pending.front());
        S.Pending.pop_front();
        ++S.Running;
      }
      Task();
    }
    {
      std::lock_guard<std::mutex> Guard(S.Lock);
      --S.Running;
    }
    S.Changed.notify_all();
    return true;
  }

  llvm::StdThreadPool &Pool;
  std::shared_ptr<State> S = std::make_shared<State>();
};

} // namespace verify
} // namespace clang

#endif
