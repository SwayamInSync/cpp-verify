// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 | FileCheck %s --check-prefix=JSON

unsigned renamed_parameter(unsigned interface_name)
  post(result == interface_name);

unsigned renamed_parameter(unsigned implementation_name) {
  return implementation_name + 1;
}

// CHECK: error: verification failed: renamed_parameter
// CHECK-SAME: implementation_name [ssa=interface_name_0] [type=u32]
// CHECK-SAME: [reason=counterexample]

// JSON: "name":"implementation_name"
// JSON-SAME: "sort":"u32"
// JSON-SAME: "ssa_name":"interface_name_0"
// JSON-SAME: "schema":"cppverify.diagnostic/1"
