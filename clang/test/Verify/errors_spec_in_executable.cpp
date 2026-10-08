// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -DALLOWED_ONLY \
// RUN:   -emit-llvm -o - %s \
// RUN:   | FileCheck %s --implicit-check-not=scaled
//
// Spec functions are never compiled, so executable code may not use them.
// Contracts, ghost code, spec and proof functions, and unevaluated operands
// may; none of those references reaches the object file.

cppverify::spec int scaled(int x) { return x * 1000; }
cppverify::spec int scaled_twice(int x) { return scaled(x) + scaled(x); }

cppverify::proof void lemma(int x)
  cppverify::post(scaled(x) == x * 1000)
{
  int value = scaled(1);
}

// CHECK: define {{.*}}allowed
int allowed(int x)
  cppverify::pre(scaled(x) >= 0)
  cppverify::post(cppverify::result == x)
{
  cppverify::ghost {
    int value = scaled(x);
    cppverify::reveal_with_fuel(scaled, 2);
  }
  cppverify::check(scaled(x) == scaled(x));
  int i = 0;
  while (i < x)
    cppverify::invariant(scaled(i) == scaled(i))
    cppverify::decreases(x - i)
  {
    i = i + 1;
  }
  decltype(scaled(x)) size = sizeof(scaled(x));
  return x + (size - size);
}

// CHECK: define {{.*}}constructed
struct Checked {
  int value;
  Checked(int v) : value(v) { cppverify::check(scaled(v) == v * 1000); }
};
int constructed(int v) { return Checked(v).value; }

template <typename T> int ghost_template(T v) {
  cppverify::ghost { int value = scaled(v); }
  return 0;
}
int ghost_instance = ghost_template(1);

#ifndef ALLOWED_ONLY
int in_return(int x) {
  return scaled(x); // expected-error {{spec function 'scaled' exists only for verification and cannot be used in executable code}}
}

int in_local(int x) {
  int y = scaled(x); // expected-error {{spec function 'scaled'}}
  return y;
}

int in_condition(int x) {
  if (scaled(x) > 0) // expected-error {{spec function 'scaled'}}
    return 1;
  return 0;
}

int (*address)(int) = scaled; // expected-error {{spec function 'scaled'}}
int in_global = scaled(2); // expected-error {{spec function 'scaled'}}

constexpr int constexpr_calls_spec(int x) {
  return scaled(x); // expected-error {{spec function 'scaled'}}
}

int in_lambda(int x) {
  auto f = [](int v) { return scaled(v); }; // expected-error {{spec function 'scaled'}}
  return f(x);
}

// A default argument is evaluated, and reported once, where it is used.
int with_default(int x = scaled(1)); // expected-error {{spec function 'scaled'}}
int uses_default() { return with_default() + with_default(); }

struct Member {
  int a = scaled(2); // expected-error {{spec function 'scaled'}}
};

struct Initialized {
  int b;
  Initialized() : b(scaled(3)) {} // expected-error {{spec function 'scaled'}}
};

template <typename T> int dependent(T v) {
  return scaled(v); // expected-error {{spec function 'scaled'}}
}
int dependent_instance = dependent(4); // expected-note {{in instantiation of function template specialization}}
#endif
