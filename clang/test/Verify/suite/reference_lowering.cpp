// RUN: %cpp-verify --lower-only --dump-ir=1,2,3,4 %s 2>&1 | FileCheck %s

void lower_reference(int &value, int next)
  pre(value == 4)
  modifies(value)
  post(value == next && old(value) == 4)
{
  value = next;
}

void lower_reference_call(int *value, int next)
  pre(value != nullptr && *value == 4)
  modifies(*value)
  post(*value == next)
{
  lower_reference(*value, next);
}

// CHECK-LABEL: fn lower_reference
// CHECK: param value
// CHECK: pre
// CHECK: load
// CHECK-NEXT: value
// CHECK: valid_ptr
// CHECK-NEXT: value
// CHECK: initialized_ptr
// CHECK-NEXT: value
// CHECK: post
// CHECK: old
// CHECK-NEXT: load
// CHECK-NEXT: value
// CHECK: modifies
// CHECK-NEXT: load
// CHECK-NEXT: value
// CHECK: body
// CHECK-NEXT: store
// CHECK-NEXT: value
// CHECK-NEXT: next
// CHECK-LABEL: passive lower_reference
// CHECK: entry
// CHECK: load
// CHECK-NEXT: value_0
// CHECK: heap_store
// CHECK: exit
// CHECK: load
// CHECK-NEXT: value_0
// CHECK-LABEL: vc lower_reference
// CHECK: heap_store
// CHECK: load
// CHECK-NEXT: value_0
// CHECK: (select __heap_0 value_0)
// CHECK: (store __heap_0 value_0
// CHECK-LABEL: fn lower_reference_call
// CHECK: call lower_reference
// CHECK-NEXT: value
// CHECK-NEXT: next
// CHECK-LABEL: passive lower_reference_call
// CHECK: load
// CHECK-NEXT: value_0
// CHECK-LABEL: vc lower_reference_call
// CHECK: load
// CHECK-NEXT: value_0
// CHECK: (select __heap_1 value_0)
