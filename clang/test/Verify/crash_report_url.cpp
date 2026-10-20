// REQUIRES: crash-recovery, backtrace
// RUN: not --crash %cpp-verify %s -- -std=c++17 2>&1 | FileCheck %s
// RUN: not --crash %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only %s 2>&1 | FileCheck %s
//
// A crash asks for a report on cpp-verify's issue tracker.

#pragma clang __debug crash

// CHECK: PLEASE submit a bug report to https://github.com/SwayamInSync/cpp-verify/issues/ and include the crash backtrace
