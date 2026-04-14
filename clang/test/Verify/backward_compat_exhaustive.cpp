// RUN: %clang_cc1 -std=c++17 -verify %s
//
// Exhaustive backward compatibility test: without -fverify-contracts, ALL 12
// contract keywords must be usable as plain identifiers. This tests more
// complex patterns than the basic backward_compat.cpp.
//
// expected-no-diagnostics

// ---------------------------------------------------------------------------
// 1. All keywords as variable names
// ---------------------------------------------------------------------------
int pre = 1;
int post = 2;
int invariant = 3;
int decreases = 4;
int ghost = 5;
int spec = 6;
int proof = 7;
int contract_assert = 8;
int old = 9;
int result = 10;
int forall = 11;
int exists = 12;

// ---------------------------------------------------------------------------
// 2. All keywords used in arithmetic
// ---------------------------------------------------------------------------
int sum_all = pre + post + invariant + decreases + ghost + spec + proof +
              contract_assert + old + result + forall + exists;

// ---------------------------------------------------------------------------
// 3. Keywords as function names
// ---------------------------------------------------------------------------
int pre_fn() { return 0; }
int post_fn() { return 0; }
int invariant_fn() { return 0; }
int decreases_fn() { return 0; }
int ghost_fn() { return 0; }
int spec_fn() { return 0; }
int proof_fn() { return 0; }

// ---------------------------------------------------------------------------
// 4. Keywords as parameter names
// ---------------------------------------------------------------------------
int use_as_param(int pre, int post, int invariant, int ghost) {
  return pre + post + invariant + ghost;
}

// ---------------------------------------------------------------------------
// 5. Keywords as struct member names
// ---------------------------------------------------------------------------
struct ContractNames {
  int pre;
  int post;
  int invariant;
  int decreases;
  int ghost;
  int result;
  int old;
};

void use_members() {
  ContractNames c;
  c.pre = 1;
  c.post = 2;
  c.invariant = 3;
  c.decreases = 4;
  c.ghost = 5;
  c.result = 6;
  c.old = 7;
}

// ---------------------------------------------------------------------------
// 6. Keywords in namespace context
// ---------------------------------------------------------------------------
namespace contract_ns {
  int pre = 100;
  int post = 200;
  int result = 300;
}

int use_ns() {
  return contract_ns::pre + contract_ns::post + contract_ns::result;
}

// ---------------------------------------------------------------------------
// 7. Keywords as template parameters (identifier usage)
// ---------------------------------------------------------------------------
template<int pre, int post>
int templated() {
  return pre + post;
}

int call_templated() {
  return templated<1, 2>();
}

// ---------------------------------------------------------------------------
// 8. Keywords in conditional expressions
// ---------------------------------------------------------------------------
int conditional_use() {
  int pre = 1;
  int post = 0;
  return pre ? pre : post;
}

// ---------------------------------------------------------------------------
// 9. Keywords as array names
// ---------------------------------------------------------------------------
int pre_arr[3] = {1, 2, 3};
int post_arr[3] = {4, 5, 6};

int array_use() {
  return pre_arr[0] + post_arr[2];
}

// ---------------------------------------------------------------------------
// 10. Keywords as typedef names
// ---------------------------------------------------------------------------
typedef int result_type;
typedef unsigned old_type;

result_type get_result() { return 42; }
old_type get_old() { return 0; }
