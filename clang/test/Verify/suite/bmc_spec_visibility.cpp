// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int identity(int value) {
  return value;
}

int valid_visible_spec(int value)
  post(result == value)
{
  contract_assert(identity(value) == value);
  return value;
}

// The assertion is true, but the solver may not use identity's definition. A
// model that interprets identity arbitrarily is not a counterexample.
int invalid_hidden_spec(int value)
  post(result == value)
{
  ghost {
    hide(identity);
    contract_assert(identity(value) == value);
  }
  return value;
}

// VERIFY-DAG: Verified: valid_visible_spec
// VERIFY-DAG: Unresolved: invalid_hidden_spec [backend=bmc{{.*}}[reason=spec.hidden]
