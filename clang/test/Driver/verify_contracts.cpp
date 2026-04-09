// Test that -fverify-contracts is forwarded from the driver to cc1, and that
// the flag is absent by default (or when -fno-verify-contracts is given).

// RUN: %clang -### -std=c++20 -fverify-contracts %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=WITH

// RUN: %clang -### -std=c++20 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=OFF

// RUN: %clang -### -std=c++20 -fno-verify-contracts %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=OFF

// -fverify-contracts must appear in the cc1 invocation.
// WITH: "-fverify-contracts"

// Without the flag (or with the explicit negation), neither form is forwarded.
// OFF-NOT: "-fverify-contracts"
// OFF-NOT: "-fno-verify-contracts"
