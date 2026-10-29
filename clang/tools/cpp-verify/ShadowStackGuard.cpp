// ThreadSanitizer builds only, without instrumentation, linked with
// --wrap=__tsan_func_entry,--wrap=__tsan_func_exit. TSan records each
// thread's calls on a shadow stack of 64 Ki frames that it does not bound, so
// a deeper nesting overwrites the runtime's own memory, and the run crashes
// or hangs at random later. This stops it at the limit with its stack.

#include <cstdio>
#include <sanitizer/common_interface_defs.h>
#include <unistd.h>

extern "C" void __real___tsan_func_entry(void *CallerPC);
extern "C" void __real___tsan_func_exit();

namespace {
thread_local unsigned long Depth;
// Interceptors push a frame too.
constexpr unsigned long MaxDepth = 64 * 1024 - 64;
} // namespace

extern "C" void __wrap___tsan_func_entry(void *CallerPC) {
  if (++Depth == MaxDepth) {
    char Message[160];
    int Length = std::snprintf(
        Message, sizeof Message,
        "cpp-verify: ThreadSanitizer shadow stack full: %lu nested calls\n",
        Depth);
    if (write(STDERR_FILENO, Message, Length) < 0)
      _exit(1);
    __sanitizer_print_stack_trace();
    _exit(1);
  }
  __real___tsan_func_entry(CallerPC);
}

extern "C" void __wrap___tsan_func_exit() {
  --Depth;
  __real___tsan_func_exit();
}
