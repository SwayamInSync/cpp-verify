// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=DUMP

// A by-value record reached through a pointer parameter records a canonical,
// target-exact object layout (with padding) on the function, and its field
// places lower to ordinary offset address arithmetic.

struct Padded {
  char c;
  int x;
};

int read_field(Padded *p)
  pre(p != nullptr && p->x >= 0)
  post(result == p->x)
{
  return p->x;
}

void write_field(Padded *p, int v)
  pre(p != nullptr)
  modifies(p->x)
  post(p->x == v)
{
  p->x = v;
}

// VERIFY-DAG: Verified: read_field
// VERIFY-DAG: Verified: write_field

// DUMP-LABEL: fn read_field
// The p->x field place lowers to base + exact byte offset 4.
// DUMP: return
// DUMP-NEXT: load
// DUMP-NEXT: +
// DUMP-NEXT: p
// DUMP-NEXT: 4
// DUMP: layout Padded record size 8 align 4
// DUMP-NEXT: leaf .c offset 0 size 1 align 1 i8
// DUMP-NEXT: leaf .x offset 4 size 4 align 4 i32

// DUMP-LABEL: fn write_field
// DUMP: store
// DUMP-NEXT: +
// DUMP-NEXT: p
// DUMP-NEXT: 4
// DUMP-NEXT: v
// DUMP: layout Padded record size 8 align 4
// DUMP-NEXT: leaf .c offset 0 size 1 align 1 i8
// DUMP-NEXT: leaf .x offset 4 size 4 align 4 i32
