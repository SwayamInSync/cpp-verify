// RUN: %clang_cc1 -triple arm64-apple-macosx14.0 -std=c++17 -fverify-contracts -fsyntax-only -verify -isystem %S/Inputs/apple %s
// RUN: %clang_cc1 -triple arm64-apple-ios17.0 -std=c++17 -fverify-contracts -fsyntax-only -verify -isystem %S/Inputs/apple %s
// RUN: not %clang_cc1 -triple arm64-apple-macosx14.0 -std=c++17 -fverify-contracts -fsyntax-only -D__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES=1 -isystem %S/Inputs/apple %s 2>&1 | FileCheck %s --check-prefix=OLD
// RUN: %clang_cc1 -triple arm64-apple-macosx14.0 -std=c++17 -fverify-contracts -E -dM -isystem %S/Inputs/apple %s | FileCheck %s --check-prefix=OFF
// RUN: %clang_cc1 -triple arm64-apple-macosx14.0 -std=c++17 -E -dM -isystem %S/Inputs/apple %s | FileCheck %s --check-prefix=ON
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -std=c++17 -fverify-contracts -E -dM -isystem %S/Inputs/apple %s | FileCheck %s --check-prefix=ON
//
// Apple's <AssertMacros.h> defines check(assertion) unless
// __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES is 0, which would expand
// cppverify::check. -fverify-contracts sets it to 0 on Apple targets unless
// the command line defines it.

#include <AssertMacros.h>

namespace cv = cppverify;

int positive(int x)
  cv::pre(x > 0)
{
  cv::check(x > 0);
  cppverify::check(x != 0);
  return x;
}

// expected-no-diagnostics
// OLD: error: expected unqualified-id
// OFF: #define __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES 0
// ON: #define __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES 1
