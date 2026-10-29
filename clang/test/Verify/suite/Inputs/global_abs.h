// The overloads of abs that libc++'s <stdlib.h> defines in the global
// namespace, and the using-declaration of its <cstdlib>.
#pragma clang system_header

inline long abs(long x) noexcept { return __builtin_labs(x); }
inline long long abs(long long x) noexcept { return __builtin_llabs(x); }

namespace std {
using ::abs;
}
