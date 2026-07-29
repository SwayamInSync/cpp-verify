// REQUIRES: cvc5
// RUN: %cpp-verify --backend=portfolio --check-ub --jobs=2 --timeout=30000 \
// RUN:   %S/Inputs/llvm_uleb128_portfolio.cpp 2>&1 | FileCheck %s

// This deliberately smaller termination/length/bounds slice is accepted by
// both Z3 and cvc5. The complete byte/round-trip proof is Z3-only because cvc5
// currently returns unknown on two of its larger obligations.

// CHECK: Verified: encode_uleb128_length [backend=portfolio]
