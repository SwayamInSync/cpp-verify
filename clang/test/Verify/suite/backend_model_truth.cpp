// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 | FileCheck %s --check-prefix=JSON
// RUN: %cpp-verify --lower-only --obligation-out=%t.obligations %s
// RUN: not %cpp-verify --obligation-in=%t.obligations --diagnostics-format=json 2>&1 | FileCheck %s --check-prefix=ARCHIVE

int underdetermined_model(int value, bool take_value)
  cppverify::pre(!take_value)
  cppverify::post(take_value ? cppverify::result == value : false)
{
  return 0;
}

// CHECK: error: verification failed: underdetermined_model
// CHECK-SAME: value [ssa=value_0] [type=i32] = <unknown>
// CHECK-SAME: [backend=z3] [reason=counterexample]

// JSON: "model":[
// JSON-SAME: {"name":"value","sort":"i32"
// JSON-SAME: "ssa_name":"value_0","value":null}
// JSON-SAME: "obligation":{"id":"{{.*}}::postcondition@{{[0-9]+}}:{{[0-9]+}}","kind":"postcondition"
// JSON-SAME: "source":{"column":19,"end_column":61,"end_line":8
// JSON-SAME: "reason":"counterexample"
// JSON-SAME: "schema":"cppverify.diagnostic/1"
// JSON-SAME: "status":"failed"

// ARCHIVE: "model":[
// ARCHIVE-SAME: {"name":"value","sort":"i32"
// ARCHIVE-SAME: "ssa_name":"value_0","value":null}
// ARCHIVE-SAME: "semantic_hash":"sha256:{{[0-9a-f]+}}"
// ARCHIVE-SAME: "source":{"column":19,"end_column":61,"end_line":8
// ARCHIVE-SAME: "status":"failed"
