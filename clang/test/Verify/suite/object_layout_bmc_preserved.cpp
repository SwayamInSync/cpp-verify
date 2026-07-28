// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=bmc --unroll=3 --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=DUMP

// The layout table is metadata on the VFunction, so it must survive the BMC
// bounded-unrolling transform. The Layer-1 dump of the unrolled function still
// carries the record layout.

struct Box {
  int lo;
  int hi;
};

int pick(Box *b, int n)
  pre(b != nullptr && n >= 0 && n <= 2)
{
  int r = b->lo;
  int i = 0;
  while (i < n)
    invariant(i >= 0 && i <= n)
  {
    r = b->hi;
    i = i + 1;
  }
  return r;
}

// VERIFY: Verified: pick

// DUMP-LABEL: fn pick
// DUMP: layout Box record size 8 align 4
// DUMP-NEXT: leaf .lo offset 0 size 4 align 4 i32
// DUMP-NEXT: leaf .hi offset 4 size 4 align 4 i32
