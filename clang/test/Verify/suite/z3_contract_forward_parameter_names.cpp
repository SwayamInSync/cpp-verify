// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int renamed_parameter(int interface_name)
  pre(interface_name >= 0)
  post(result == interface_name);

int renamed_parameter(int implementation_name) {
  return implementation_name;
}

int unnamed_interface_parameter(int)
  post(result == 7);

int unnamed_interface_parameter(int implementation_name) {
  return 7;
}

// VERIFY-DAG: Verified: renamed_parameter
// VERIFY-DAG: Verified: unnamed_interface_parameter
