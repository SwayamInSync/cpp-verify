// RUN: %clang -### -std=c++20 -fverify-contracts %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=WITH-VERIFY
// RUN: %clang -### -std=c++20 -fverify-contracts -fno-verify %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=NO-VERIFY
// RUN: %clang -### -std=c++20 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=OFF

// WITH-VERIFY: "-fverify-contracts"
// WITH-VERIFY-NOT: "-fno-verify"

// NO-VERIFY: "-fverify-contracts"
// NO-VERIFY: "-fno-verify"
// NO-VERIFY-NOT: "-fverify"

// OFF-NOT: "-fverify-contracts"
// OFF-NOT: "-fverify"
// OFF-NOT: "-fno-verify"

int main() { return 0; }