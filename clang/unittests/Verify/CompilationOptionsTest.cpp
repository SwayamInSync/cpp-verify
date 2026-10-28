//===--- CompilationOptionsTest.cpp - -fverify-* options -----------------===//
#include "../../lib/Verify/Driver/CppVerifyIntegration.h"
#include "clang/Frontend/FrontendOptions.h"
#include "gtest/gtest.h"

using namespace clang;
using namespace clang::verify;

namespace {

TEST(CompilationOptionsTest, Defaults) {
  FrontendOptions Options;
  VerifyOptions Opts = compilationOptions(Options);
  VerifyOptions Tool;
  EXPECT_EQ(Opts.Backend, BackendKind::Z3);
  EXPECT_EQ(Opts.SolverTimeoutMs, Tool.SolverTimeoutMs);
  EXPECT_EQ(Opts.CollectionTimeoutMs, Tool.CollectionTimeoutMs);
  EXPECT_EQ(Opts.FunctionTimeoutMs, Tool.FunctionTimeoutMs);
  EXPECT_EQ(Opts.Jobs, 1u);
  EXPECT_TRUE(Opts.ProofCachePath.empty());
  EXPECT_TRUE(Opts.ReportPath.empty());
  EXPECT_TRUE(Opts.QuietWithoutFunctions);
}

TEST(CompilationOptionsTest, EachOption) {
  FrontendOptions Options;
  Options.VerifyTimeoutMs = 5000;
  Options.VerifyJobs = 4;
  Options.VerifyCache = "cache";
  Options.VerifyReport = "a.o.cppverify.json";
  Options.VerifyContractsOut = "a.o.cppverify";
  VerifyOptions Opts = compilationOptions(Options);
  EXPECT_EQ(Opts.SolverTimeoutMs, 5000u);
  EXPECT_EQ(Opts.CollectionTimeoutMs, 10000u);
  EXPECT_EQ(Opts.FunctionTimeoutMs, 50000u);
  EXPECT_EQ(Opts.Jobs, 4u);
  EXPECT_EQ(Opts.ProofCachePath, "cache");
  EXPECT_EQ(Opts.ReportPath, "a.o.cppverify.json");
  EXPECT_EQ(Opts.ContractsOut, "a.o.cppverify");
}

TEST(CompilationOptionsTest, Backends) {
  const std::pair<FrontendOptions::CppVerifyBackend, BackendKind> Cases[] = {
      {FrontendOptions::CppVerifyBackend::Z3, BackendKind::Z3},
      {FrontendOptions::CppVerifyBackend::CVC5, BackendKind::CVC5},
      {FrontendOptions::CppVerifyBackend::Portfolio, BackendKind::Portfolio},
      {FrontendOptions::CppVerifyBackend::Race, BackendKind::Race},
      {FrontendOptions::CppVerifyBackend::BMC, BackendKind::BMC}};
  for (const auto &[Option, Backend] : Cases) {
    FrontendOptions Options;
    Options.VerifyBackend = Option;
    EXPECT_EQ(compilationOptions(Options).Backend, Backend);
  }
}

TEST(CompilationOptionsTest, NoTimeout) {
  // 0 disables every time limit, as cpp-verify --timeout=0 does.
  FrontendOptions Options;
  Options.VerifyTimeoutMs = 0;
  VerifyOptions Opts = compilationOptions(Options);
  EXPECT_EQ(Opts.SolverTimeoutMs, 0u);
  EXPECT_EQ(Opts.CollectionTimeoutMs, 0u);
  EXPECT_EQ(Opts.FunctionTimeoutMs, 0u);
}

TEST(CompilationOptionsTest, ExtremeValues) {
  FrontendOptions Options;
  Options.VerifyJobs = 0;
  Options.VerifyTimeoutMs = 4000000000u;
  VerifyOptions Opts = compilationOptions(Options);
  EXPECT_EQ(Opts.Jobs, 1u);
  EXPECT_EQ(Opts.SolverTimeoutMs, 4000000000u);
  // Too long to scale: no bound, as cpp-verify does.
  EXPECT_EQ(Opts.CollectionTimeoutMs, 0u);
  EXPECT_EQ(Opts.FunctionTimeoutMs, 0u);
}

} // namespace
