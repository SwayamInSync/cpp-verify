// RUN: %cpp-verify --jobs=1 %s -- --target=x86_64-pc-windows-msvc 2>&1 \
// RUN:   | FileCheck %s
//
// Only the functions the verifier converts or reports are named. A template
// or member function without contracts is neither, so it is never mangled;
// under the Microsoft ABI, whose mangler cannot mangle a dependent type, the
// templates of the standard headers made every run fail.

template <unsigned N> int length(const char (&s)[N]) { return N; }

template <class T> struct Box {
  T get() const { return v; }
  T v;
};

struct Plain {
  int get() const { return 0; }
};

int abs_value(int x)
  cppverify::pre(x > -2147483647 - 1)
  cppverify::post(cppverify::result >= 0)
{
  return x < 0 ? -x : x;
}

// CHECK-NOT: error
// CHECK: Verified: abs_value [backend=z3]
// CHECK-NOT: error
