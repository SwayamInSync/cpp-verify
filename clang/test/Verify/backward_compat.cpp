// RUN: %clang_cc1 -std=c++17 -verify %s
//
// Week-2 milestone test: without -fverify-contracts, all contract keywords
// are valid identifiers and the file compiles without any diagnostics.
//
// expected-no-diagnostics

int pre = 1;
int post = 2;
int invariant = 3;
int decreases = 4;
int ghost = 5;
int result = pre + post + invariant + decreases + ghost;

// 'spec', 'proof', 'contract_assert', 'forall', 'exists', 'old' are also
// plain identifiers without the flag.
int spec = 6;
int proof = 7;
int old = 8;

int forall_value = spec + proof + old;
