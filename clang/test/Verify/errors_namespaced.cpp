// RUN: %clang_cc1 -std=c++20 -fverify-contracts -fsyntax-only -verify %s
// RUN: not %clang_cc1 -std=c++20 -fverify-contracts -fsyntax-only -fdiagnostics-parseable-fixits %s 2>&1 | FileCheck %s
//
// A construct written where it does not belong, misspelled, or without its
// qualifier gets one error that says how to write it, with a fix-it where
// there is one.

namespace cv = cppverify;

int misspelled(int x) cv::pree(x > 0) { return x; } // expected-error {{no cpp-verify construct named 'cppverify::pree'; did you mean 'cppverify::pre'?}}
// CHECK: fix-it:"{{.*}}":{[[@LINE-1]]:27-[[@LINE-1]]:31}:"pre"

int unknown(int x) cv::foo(x) { return x; } // expected-error {{no cpp-verify construct named 'cppverify::foo'}}

int cxx26(int x) pre(x > 0) { return x; } // expected-error {{C++26 contract specifiers are not supported; a cpp-verify precondition is written 'cppverify::pre'}}
// CHECK: fix-it:"{{.*}}":{[[@LINE-1]]:18-[[@LINE-1]]:21}:"cppverify::pre"

int bare_clause(int *p) modifies(*p) { return *p; } // expected-error {{'modifies' is a cpp-verify construct only when qualified: write 'cppverify::modifies'}}
// CHECK: fix-it:"{{.*}}":{[[@LINE-1]]:25-[[@LINE-1]]:33}:"cppverify::modifies"

int bare_result(int n) cv::post(result == n) { return n; } // expected-error {{'result' is a cpp-verify construct only when qualified: write 'cppverify::result'}}

int old_name(int x) {
  contract_assert(x > 0); // expected-error {{'contract_assert' is a cpp-verify construct only when qualified: write 'cppverify::check'}}
  // CHECK: fix-it:"{{.*}}":{[[@LINE-1]]:3-[[@LINE-1]]:18}:"cppverify::check"
  return x;
}

int with_using(int n) {
  using namespace cppverify;
  return forall(k, 0, n, k >= 0); // expected-error {{'forall' is a cpp-verify construct only when qualified: write 'cppverify::forall'}}
}

int clause_in_body(int x) {
  cv::pre(x > 0); // expected-error {{'cppverify::pre' follows a function's parameter list}}
  return x;
}

cv::check(true); // expected-error {{'cppverify::check' is a statement in a function body}}

int loop_clause_in_function(int n) cv::invariant(n > 0) { return n; } // expected-error {{'cppverify::invariant' goes between a loop's head and its body}}

int trigger_outside(int n) cv::pre(cv::trigger(n) > 0) { return n; } // expected-error {{'cppverify::trigger' marks a term of a quantifier body}}

int result_in_pre(int n) cv::pre(cv::result > 0) { return n; } // expected-error {{'cppverify::result' can only be used in postconditions}}

// Without a visible declaration of the name only.
int check(int);
int calls_own_check(int x) { return check(x); }
