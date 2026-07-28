// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=DUMP

// A self-referential, pointer-bearing record has a finite layout: the `next`
// field is emitted as a single Ptr leaf and the layout builder does not recurse
// into the pointee, so construction terminates without infinite expansion.

struct Node {
  int value;
  Node *next;
};

unsigned long node_size()
  post(result == sizeof(Node))
{
  return sizeof(Node);
}

// VERIFY: Verified: node_size

// DUMP-LABEL: fn node_size
// DUMP: layout Node record size 16 align 8
// DUMP-NEXT: leaf .value offset 0 size 4 align 4 i32
// DUMP-NEXT: leaf .next offset 8 size 8 align 8 ptr(16)
// The pointer leaf stops here: no recursive expansion of the pointee.
// DUMP-NOT: leaf .next.
