// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s -- 2>&1 | FileCheck %s --check-prefix=JSON

unsigned renamed_parameter(unsigned interface_name)
  cppverify::post(cppverify::result == interface_name);

unsigned renamed_parameter(unsigned implementation_name) {
  return implementation_name + 1;
}

// CHECK: error: verification failed: renamed_parameter
// CHECK-SAME: [reason=counterexample]
// CHECK: note: counterexample: implementation_name = 0, result = 1

// JSON: "name":"implementation_name"
// JSON-SAME: "sort":"u32"
// JSON-SAME: "ssa_name":"interface_name_0"
// JSON-SAME: "schema":"cppverify.diagnostic/2"
