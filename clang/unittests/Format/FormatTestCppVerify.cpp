//===- unittest/Format/FormatTestCppVerify.cpp ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "FormatTestBase.h"

#define DEBUG_TYPE "format-test"

namespace clang {
namespace format {
namespace test {
namespace {

class FormatTestCppVerify : public test::FormatTestBase {};

TEST_F(FormatTestCppVerify, FunctionClauses) {
  verifyFormat("int max_index(const int *a, int n)\n"
               "  cppverify::pre(n > 0 && cppverify::valid(a, n))\n"
               "  cppverify::post(0 <= cppverify::result && "
               "cppverify::result < n)\n"
               "{\n"
               "  return 0;\n"
               "}",
               "int max_index(const int *a, int n) cppverify::pre(n > 0 && "
               "cppverify::valid(a, n)) cppverify::post(0 <= cppverify::result "
               "&& cppverify::result < n) { return 0; }");
  verifyFormat("int declared(int x)\n"
               "  cppverify::pre(x > 0)\n"
               "  cppverify::post(cppverify::result > 0);",
               "int declared(int x) cppverify::pre(x > 0) "
               "cppverify::post(cppverify::result > 0);");
  verifyFormat("void swap(int *a, int *b) const noexcept\n"
               "  ::cppverify::modifies(*a, *b)\n"
               "{}");
}

TEST_F(FormatTestCppVerify, AliasesAndMacros) {
  verifyFormat("namespace cv = cppverify;\n"
               "cv::spec bool even(int n)\n"
               "  cv::inductive\n"
               "{\n"
               "  return n == 0 || even(n - 2);\n"
               "}");
  verifyFormat("auto f(int x) -> int\n"
               "  cv::pre(x > 0)\n"
               "  PRE(x < 100)\n"
               "{\n"
               "  return x;\n"
               "}");
  verifyFormat("cv::spec int total(const int *a, int n)\n"
               "  cv::reads(a, n)\n"
               "  cv::decreases(n) by { lemma(n); }\n"
               "{\n"
               "  return n;\n"
               "}");
}

TEST_F(FormatTestCppVerify, LoopClauses) {
  verifyFormat("void f(int n) {\n"
               "  for (int i = 0; i < n; ++i)\n"
               "    cppverify::invariant(0 <= i && i <= n)\n"
               "    cppverify::decreases(n - i)\n"
               "  {\n"
               "    g(i);\n"
               "  }\n"
               "  while (n > 0)\n"
               "    cppverify::decreases(n)\n"
               "  {\n"
               "    --n;\n"
               "  }\n"
               "  do {\n"
               "    ++n;\n"
               "  } while (n < 10)\n"
               "    cppverify::invariant(n <= 10)\n"
               "    cppverify::decreases(10 - n);\n"
               "}");
}

TEST_F(FormatTestCppVerify, OrdinaryCodeIsUnchanged) {
  // A call statement after a loop head or a condition is the body.
  verifyFormat("void f(int n) {\n"
               "  while (n > 0)\n"
               "    other::invariant(n);\n"
               "  if (n)\n"
               "    other::post(n);\n"
               "}");
  verifyFormat("int pre(int post) { return post; }");
}

} // namespace
} // namespace test
} // namespace format
} // namespace clang
