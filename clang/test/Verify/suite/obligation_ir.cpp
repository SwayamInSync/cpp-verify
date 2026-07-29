// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --lower-only --dump-ir=3 %s > %t.first 2>&1
// RUN: %cpp-verify --lower-only --dump-ir=3 %s > %t.second 2>&1
// RUN: diff %t.first %t.second
// RUN: FileCheck %s --check-prefix=OBLIGATION < %t.first
// RUN: %cpp-verify --lower-only --dump-ir=3,4 %s 2>&1 | FileCheck %s --check-prefix=LAYERS
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=Z3
// RUN: %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: rm -f %t.first.obligations %t.second.obligations
// RUN: %cpp-verify --lower-only --obligation-out=%t.first.obligations %s
// RUN: %cpp-verify --lower-only --obligation-out=%t.second.obligations %s
// RUN: cmp %t.first.obligations %t.second.obligations
// RUN: cp %s %t.relocated.cpp
// RUN: %cpp-verify --lower-only --dump-ir=3 %t.relocated.cpp 2>&1 | grep 'semantic-hash' > %t.relocated.hashes
// RUN: grep 'semantic-hash' %t.first > %t.original.hashes
// RUN: diff %t.original.hashes %t.relocated.hashes

int canonical_obligations(int x)
  pre(x >= 0 && x < 10)
  post(result == x + 1)
{
  contract_assert(x >= 0);
  int next = x + 1;
  contract_assert(next > x);
  return next;
}

// OBLIGATION-LABEL: vc canonical_obligations
// OBLIGATION-NEXT: schema cppverify.obligation/1
// OBLIGATION-NEXT: semantic-hash sha256:056efcca83927d8813a2695e996a985fba0dbf7ac00a85c515f07eb763efac1a
// OBLIGATION-NEXT: identity [[IDENTITY:fn_[0-9a-f]+]]
// OBLIGATION-NEXT: features mathematical-integers, bit-vectors, pointers, heap-arrays
// OBLIGATION-NEXT: counterexample
// OBLIGATION: x_0 : bitvector32
// OBLIGATION: obligations [[COUNT:[1-9][0-9]*]]
// OBLIGATION: obligation [[IDENTITY]]::obligation:1 assertion
// OBLIGATION-NEXT: semantic-hash sha256:39fb2099758d697c777e8a21ce4a4cd2e7f5421630f5886a26976c6b57cff9df
// OBLIGATION-NEXT: source {{[1-9][0-9]*}}
// OBLIGATION: obligation [[IDENTITY]]::obligation:{{[1-9][0-9]*}} postcondition
// OBLIGATION-NEXT: semantic-hash sha256:{{[0-9a-f]+}}
// OBLIGATION-NEXT: source {{[1-9][0-9]*}}
// OBLIGATION: Lowered: canonical_obligations

// LAYERS-LABEL: vc canonical_obligations
// LAYERS: counterexample
// LAYERS: next_1 : bitvector32
// LAYERS: obligations
// LAYERS: ======
// LAYERS: (bvadd x_0 #x00000001)
// LAYERS: Lowered: canonical_obligations

// Z3: Verified: canonical_obligations
// BMC: Verified: canonical_obligations
