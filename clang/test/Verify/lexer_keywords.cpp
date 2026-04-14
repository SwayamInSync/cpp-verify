// RUN: %clang_cc1 -std=c++17 -fverify-contracts -dump-tokens %s 2>&1 | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -dump-tokens %s 2>&1 | FileCheck -check-prefix=NOCONTRACT %s
//
// Exhaustive lexer test: verify that all 12 contract keywords are tokenized
// as keywords when -fverify-contracts is enabled, and as identifiers without it.

// With -fverify-contracts, each word is a keyword token:
//   dump-tokens format: <token-kind> '<spelling>' ...
// CHECK:      pre 'pre'
// CHECK-NEXT: post 'post'
// CHECK-NEXT: invariant 'invariant'
// CHECK-NEXT: decreases 'decreases'
// CHECK-NEXT: ghost 'ghost'
// CHECK-NEXT: spec 'spec'
// CHECK-NEXT: proof 'proof'
// CHECK-NEXT: contract_assert 'contract_assert'
// CHECK-NEXT: forall 'forall'
// CHECK-NEXT: exists 'exists'
// CHECK-NEXT: old 'old'
// CHECK-NEXT: result 'result'

// Without -fverify-contracts, all become plain identifiers:
// NOCONTRACT:      identifier 'pre'
// NOCONTRACT-NEXT: identifier 'post'
// NOCONTRACT-NEXT: identifier 'invariant'
// NOCONTRACT-NEXT: identifier 'decreases'
// NOCONTRACT-NEXT: identifier 'ghost'
// NOCONTRACT-NEXT: identifier 'spec'
// NOCONTRACT-NEXT: identifier 'proof'
// NOCONTRACT-NEXT: identifier 'contract_assert'
// NOCONTRACT-NEXT: identifier 'forall'
// NOCONTRACT-NEXT: identifier 'exists'
// NOCONTRACT-NEXT: identifier 'old'
// NOCONTRACT-NEXT: identifier 'result'

pre post invariant decreases ghost spec proof contract_assert forall exists old result
