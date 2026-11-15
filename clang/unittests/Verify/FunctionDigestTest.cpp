//===- unittests/Verify/FunctionDigestTest.cpp ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "../../lib/Verify/IR/VHash.h"
#include "gtest/gtest.h"

using namespace clang;
using namespace clang::verify;

namespace {

VType intType() { return VType::makeInt32(VIntMode::Machine); }

std::unique_ptr<VExpr> var(const char *Name, SourceLocation Loc) {
  return std::make_unique<VVarExpr>(Name, intType(), Loc);
}

/// int f(int x) post(result == twice(x)) { t = g(x); return t + Addend; }
VFunction function(unsigned Offset, int Addend = 1) {
  auto At = [&](unsigned N) {
    return SourceLocation::getFromRawEncoding(Offset + N);
  };
  VFunction Fn;
  Fn.Name = "f";
  Fn.Identity = "c:@F@f";
  Fn.ReturnType = intType();
  Fn.DeclLoc = At(1);
  Fn.Extent = SourceRange(At(1), At(90));
  Fn.Params.emplace_back("x", intType());
  std::vector<std::unique_ptr<VExpr>> SpecArgs;
  SpecArgs.push_back(var("x", At(10)));
  Fn.Postconditions.push_back(std::make_unique<VBinOpExpr>(
      VBinOp::Eq, std::make_unique<VResultExpr>(intType(), At(8)),
      std::make_unique<VSpecCallExpr>("twice", "c:@F@twice",
                                      std::move(SpecArgs), intType(), At(9)),
      VType::makeBool(), At(7)));
  std::vector<std::unique_ptr<VExpr>> CallArgs;
  CallArgs.push_back(var("x", At(21)));
  Fn.Body.push_back(std::make_unique<VCallStmt>(
      "g", "c:@F@g", std::move(CallArgs), "t", At(20)));
  Fn.Body.push_back(std::make_unique<VReturnStmt>(
      std::make_unique<VBinOpExpr>(
          VBinOp::Add, var("t", At(31)),
          std::make_unique<VLiteralExpr>(Addend, intType(), At(32)), intType(),
          At(30)),
      At(29)));
  return Fn;
}

TEST(FunctionDigest, IgnoresWhereTheFunctionIs) {
  EXPECT_EQ(digestVFunction(function(100)).Hash,
            digestVFunction(function(5000)).Hash);
}

TEST(FunctionDigest, CoversWhetherAPositionIsThere) {
  VFunction Marked = function(100);
  Marked.UnmeasuredLoop = SourceLocation::getFromRawEncoding(140);
  EXPECT_NE(digestVFunction(function(100)).Hash, digestVFunction(Marked).Hash);
}

TEST(FunctionDigest, CoversTheBody) {
  EXPECT_NE(digestVFunction(function(100, 1)).Hash,
            digestVFunction(function(100, 2)).Hash);
}

TEST(FunctionDigest, InterfaceLeavesTheBodyOut) {
  EXPECT_EQ(digestVFunction(function(100, 1), VDigestScope::Interface).Hash,
            digestVFunction(function(100, 2), VDigestScope::Interface).Hash);
  EXPECT_NE(digestVFunction(function(100), VDigestScope::Interface).Hash,
            digestVFunction(function(100)).Hash);
}

TEST(FunctionDigest, InterfaceCoversTheContractAndBodySummaries) {
  const std::string Base =
      digestVFunction(function(100), VDigestScope::Interface).Hash;
  VFunction Contract = function(100);
  Contract.Postconditions.push_back(
      std::make_unique<VLiteralExpr>(1, VType::makeBool(), SourceLocation()));
  EXPECT_NE(Base, digestVFunction(Contract, VDigestScope::Interface).Hash);
  VFunction Writes = function(100);
  Writes.MayWriteHeap = true;
  EXPECT_NE(Base, digestVFunction(Writes, VDigestScope::Interface).Hash);
  VFunction Lends = function(100);
  Lends.LendableScalarParams.insert("x");
  EXPECT_NE(Base, digestVFunction(Lends, VDigestScope::Interface).Hash);
  VFunction Returns = function(100);
  Returns.ReturnedPointers.emplace();
  EXPECT_NE(Base, digestVFunction(Returns, VDigestScope::Interface).Hash);
}

TEST(FunctionDigest, CoversLayouts) {
  VFunction Laid = function(100);
  VObjectLayout Layout;
  Layout.TypeIdentity = "Pair";
  Layout.SizeBytes = 8;
  Laid.Layouts.push_back(Layout);
  VFunction Larger = function(100);
  Layout.SizeBytes = 12;
  Larger.Layouts.push_back(Layout);
  EXPECT_NE(digestVFunction(Laid).Hash, digestVFunction(Larger).Hash);
}

TEST(FunctionDigest, NamesWhatTheFunctionNames) {
  VFunction Fn = function(100);
  Fn.SpecFuel["c:@F@fueled"] = 2;
  Fn.HiddenSpecs.insert("c:@F@hidden");
  const std::set<std::string> Whole = digestVFunction(Fn).References;
  EXPECT_EQ(Whole, (std::set<std::string>{"c:@F@fueled", "c:@F@g",
                                          "c:@F@hidden", "c:@F@twice"}));
  // The call of g is in the body.
  const std::set<std::string> Interface =
      digestVFunction(Fn, VDigestScope::Interface).References;
  EXPECT_EQ(Interface, (std::set<std::string>{"c:@F@fueled", "c:@F@hidden",
                                              "c:@F@twice"}));
}

} // namespace
