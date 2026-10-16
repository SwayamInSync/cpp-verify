// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify=expected %s
// RUN: %clang_cc1 -std=c++14 -fverify-contracts -verify=expected,cxx14 %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -DALLOWED_ONLY \
// RUN:   -emit-llvm -o - %s \
// RUN:   | FileCheck %s --implicit-check-not=scaled
//
// A generic lambda's body is checked in each specialization of its call
// operator, as executable code where the lambda is written. C++17 makes the
// call operator constexpr, so a specialization is instantiated at its first
// call, before the enclosing code is checked; C++14 instantiates it at the end
// of the file, after.

cppverify::spec int scaled(int x) { return x * 1000; }

cppverify::spec int in_spec(int v) {
  auto f = [](auto x) -> int { return scaled(x); };
  return f(v);
}

cppverify::proof void in_proof(int v) {
  auto f = [](auto x) -> int { return scaled(x); };
  int value = f(v);
}

// CHECK: define {{.*}}in_ghost
int in_ghost(int v) {
  cppverify::ghost {
    auto f = [](auto x) -> int { return scaled(x); };
    int value = f(v);
  }
  cppverify::check([](auto x) -> int { return scaled(x); }(v) == scaled(v));
  auto checked = [](auto x) -> int {
    cppverify::check(scaled(1) == 1000);
    return x;
  };
  return checked(v);
}

#ifndef ALLOWED_ONLY
int in_body(int x) {
  auto f = [](auto v) -> int { return scaled(v); }; // expected-error {{spec function 'scaled' exists only for verification and cannot be used in executable code}}
  return f(x) + f(1L); // cxx14-note {{in instantiation of function template specialization}}
}

int nested(int x) {
  auto outer = [](auto v) -> int {
    auto inner = [](auto w) -> int { return scaled(w); }; // expected-error {{spec function 'scaled'}}
    return inner(v); // cxx14-note {{in instantiation of function template specialization}}
  };
  return outer(x); // cxx14-note {{in instantiation of function template specialization}}
}

int in_global = [](auto v) -> int { return scaled(v); }(5); // expected-error {{spec function 'scaled'}} cxx14-note {{in instantiation of function template specialization}}

#if __cplusplus >= 201703L
struct Holder {
  static constexpr auto fn = [](auto v) -> int { return scaled(v); }; // expected-error {{spec function 'scaled'}}
};
int use_holder() { return Holder::fn(6); } // expected-note {{in instantiation of function template specialization}}
#endif

namespace adl {
struct S {};
cppverify::spec int pick(S) { return 1; }
} // namespace adl
int dependent_lookup() {
  return [](auto s) -> int { return pick(s); }(adl::S{}); // expected-error {{spec function 'pick'}} cxx14-note {{in instantiation of function template specialization}}
}

template <typename T> int in_template(T v) {
  auto f = [](auto w) -> int { return scaled(w); }; // expected-error {{spec function 'scaled'}}
  return f(v); // expected-note {{in instantiation of function template specialization}}
}
int template_instance = in_template(7); // expected-note {{in instantiation of function template specialization}}
#endif
