// Verify that all 12 KEYCONTRACT keywords are lexed correctly.
//
// With -fverify-contracts:    each name lexes as a keyword token.
// Without -fverify-contracts: each name lexes as an identifier (no conflict
//                             with existing C++ code).

// --- dump-tokens: WITH flag — expect keyword tokens ---
// RUN: %clang_cc1 -std=c++20 -fverify-contracts -dump-tokens %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=KW

// --- dump-tokens: WITHOUT flag — expect identifier tokens ---
// RUN: %clang_cc1 -std=c++20 -dump-tokens %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=ID

// --- __is_identifier: WITH flag (-DWITH_FLAG selects the right assertions) ---
// RUN: %clang_cc1 -std=c++20 -fverify-contracts -DWITH_FLAG -fsyntax-only %s

// --- __is_identifier: WITHOUT flag ---
// RUN: %clang_cc1 -std=c++20 -fsyntax-only %s

// ==========================================================================
// Section 1: FileCheck patterns for dump-tokens runs
//
// dump-tokens is lex-only; syntax does not matter.  The tokens that satisfy
// these checks come from the variable declarations in Section 3, which are
// compiled by every dump-tokens run (neither run defines WITH_FLAG).
//
// KW-DAG checks that each name appears as a keyword token.
// ID-DAG checks that each name appears as an identifier token.
// ==========================================================================

// KW-DAG: pre 'pre'
// KW-DAG: post 'post'
// KW-DAG: invariant 'invariant'
// KW-DAG: decreases 'decreases'
// KW-DAG: ghost 'ghost'
// KW-DAG: spec 'spec'
// KW-DAG: proof 'proof'
// KW-DAG: contract_assert 'contract_assert'
// KW-DAG: forall 'forall'
// KW-DAG: exists 'exists'
// KW-DAG: old 'old'
// KW-DAG: result 'result'

// ID-DAG: identifier 'pre'
// ID-DAG: identifier 'post'
// ID-DAG: identifier 'invariant'
// ID-DAG: identifier 'decreases'
// ID-DAG: identifier 'ghost'
// ID-DAG: identifier 'spec'
// ID-DAG: identifier 'proof'
// ID-DAG: identifier 'contract_assert'
// ID-DAG: identifier 'forall'
// ID-DAG: identifier 'exists'
// ID-DAG: identifier 'old'
// ID-DAG: identifier 'result'

// ==========================================================================
// Section 2: __is_identifier() static assertions
//
// __is_identifier(X) is a preprocessor built-in: it expands to 0 or 1
// *before* the C++ parser runs, so the parser never sees the keyword token
// inside the parens.  The result is a pure integer literal.
//
// WITH_FLAG  → -fverify-contracts active → all 12 are keywords  → expect 0
// !WITH_FLAG → flag absent               → all 12 are identifiers → expect 1
// ==========================================================================

#ifdef WITH_FLAG
static_assert(!__is_identifier(pre),             "pre must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(post),            "post must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(invariant),       "invariant must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(decreases),       "decreases must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(ghost),           "ghost must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(spec),            "spec must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(proof),           "proof must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(contract_assert), "contract_assert must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(forall),          "forall must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(exists),          "exists must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(old),             "old must be a keyword with -fverify-contracts");
static_assert(!__is_identifier(result),          "result must be a keyword with -fverify-contracts");
#else
// ==========================================================================
// Section 3: identifier-mode checks + token source for dump-tokens runs
//
// This block is compiled by:
//   - the two dump-tokens runs (no WITH_FLAG defined)
//   - the fsyntax-only run WITHOUT -fverify-contracts
//
// The variable declarations give dump-tokens the tokens to match against.
// The static_assert lines verify backward compatibility.
// ==========================================================================

// Backward compatibility: all names remain valid C++ identifiers.
static_assert(__is_identifier(pre),             "pre must be an identifier without -fverify-contracts");
static_assert(__is_identifier(post),            "post must be an identifier without -fverify-contracts");
static_assert(__is_identifier(invariant),       "invariant must be an identifier without -fverify-contracts");
static_assert(__is_identifier(decreases),       "decreases must be an identifier without -fverify-contracts");
static_assert(__is_identifier(ghost),           "ghost must be an identifier without -fverify-contracts");
static_assert(__is_identifier(spec),            "spec must be an identifier without -fverify-contracts");
static_assert(__is_identifier(proof),           "proof must be an identifier without -fverify-contracts");
static_assert(__is_identifier(contract_assert), "contract_assert must be an identifier without -fverify-contracts");
static_assert(__is_identifier(forall),          "forall must be an identifier without -fverify-contracts");
static_assert(__is_identifier(exists),          "exists must be an identifier without -fverify-contracts");
static_assert(__is_identifier(old),             "old must be an identifier without -fverify-contracts");
static_assert(__is_identifier(result),          "result must be an identifier without -fverify-contracts");

// Declarations whose names produce the keyword/identifier tokens that the
// dump-tokens FileCheck patterns match against.  With -fverify-contracts each
// name lexes as its keyword token; without it, as an identifier token.
// (dump-tokens is lex-only so no parse error occurs in either case.)
int pre, post, invariant, decreases, ghost, spec, proof;
int contract_assert, forall, exists, old, result;
#endif
