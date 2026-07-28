// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=DUMP

// A constant-array type encountered in a function records a canonical layout
// with element count, stride, and recursively flattened element leaves. This
// slice only builds and dumps the layout; array *values* remain unsupported by
// execution (see object_layout_array_fails_closed.cpp).

unsigned long array_layout()
  post(result == sizeof(int[4]))
{
  return sizeof(int[4]);
}

// VERIFY: Verified: array_layout

// DUMP-LABEL: fn array_layout
// DUMP: layout int[4] array size 16 align 4 count 4 stride 4
// DUMP-NEXT: leaf [*] offset 0 size 4 align 4 repeat 4 stride 4 i32
