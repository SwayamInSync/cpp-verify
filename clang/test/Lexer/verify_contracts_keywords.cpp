// cpp-verify writes its constructs qualified, cppverify::pre(...), so no word
// is reserved: with or without -fverify-contracts each construct word, and
// the former keyword contract_assert, lexes as an identifier and remains a
// valid name.
//
// RUN: %clang_cc1 -std=c++20 -fverify-contracts -dump-tokens %s 2>&1 | FileCheck %s
// RUN: %clang_cc1 -std=c++20 -dump-tokens %s 2>&1 | FileCheck %s
// RUN: %clang_cc1 -std=c++20 -fverify-contracts -fsyntax-only %s
// RUN: %clang_cc1 -std=c++20 -fsyntax-only %s

// CHECK-DAG: identifier 'pre' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'post' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'modifies' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'aliases' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'recommends' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'reads' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'when' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'decreases' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'inductive' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'behavior' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'complete_behaviors' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'disjoint_behaviors' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'invariant' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'type_invariant' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'spec' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'proof' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'ghost' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'check' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'calc' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'reveal_with_fuel' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'hide' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'reveal' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'forall' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'exists' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'choose' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'old' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'result' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'trigger' {{.*}}verify_contracts_keywords.cpp
// CHECK-DAG: identifier 'contract_assert' {{.*}}verify_contracts_keywords.cpp

static_assert(__is_identifier(pre), "pre is an identifier");
static_assert(__is_identifier(post), "post is an identifier");
static_assert(__is_identifier(modifies), "modifies is an identifier");
static_assert(__is_identifier(aliases), "aliases is an identifier");
static_assert(__is_identifier(recommends), "recommends is an identifier");
static_assert(__is_identifier(reads), "reads is an identifier");
static_assert(__is_identifier(when), "when is an identifier");
static_assert(__is_identifier(decreases), "decreases is an identifier");
static_assert(__is_identifier(inductive), "inductive is an identifier");
static_assert(__is_identifier(behavior), "behavior is an identifier");
static_assert(__is_identifier(complete_behaviors), "complete_behaviors is an identifier");
static_assert(__is_identifier(disjoint_behaviors), "disjoint_behaviors is an identifier");
static_assert(__is_identifier(invariant), "invariant is an identifier");
static_assert(__is_identifier(type_invariant), "type_invariant is an identifier");
static_assert(__is_identifier(spec), "spec is an identifier");
static_assert(__is_identifier(proof), "proof is an identifier");
static_assert(__is_identifier(ghost), "ghost is an identifier");
static_assert(__is_identifier(check), "check is an identifier");
static_assert(__is_identifier(calc), "calc is an identifier");
static_assert(__is_identifier(reveal_with_fuel), "reveal_with_fuel is an identifier");
static_assert(__is_identifier(hide), "hide is an identifier");
static_assert(__is_identifier(reveal), "reveal is an identifier");
static_assert(__is_identifier(forall), "forall is an identifier");
static_assert(__is_identifier(exists), "exists is an identifier");
static_assert(__is_identifier(choose), "choose is an identifier");
static_assert(__is_identifier(old), "old is an identifier");
static_assert(__is_identifier(result), "result is an identifier");
static_assert(__is_identifier(trigger), "trigger is an identifier");
static_assert(__is_identifier(contract_assert), "contract_assert is an identifier");

int pre, post, modifies, aliases, recommends, reads, when, decreases, inductive, behavior, complete_behaviors, disjoint_behaviors, invariant, type_invariant, spec, proof, ghost, check, calc, reveal_with_fuel, hide, reveal, forall, exists, choose, old, result, trigger, contract_assert;
