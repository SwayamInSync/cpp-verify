//===--- Presburger.h - Deciding linear integer formulas --------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Presburger arithmetic: first-order formulas over the integers with
// addition, constant multiples, order, and divisibility by constants. The
// certifier reduces a quantified formula, once a model fixes everything but
// its binders, to this fragment and decides it exactly by Cooper's quantifier
// elimination.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_VERIFY_BACKEND_PRESBURGER_H
#define LLVM_CLANG_VERIFY_BACKEND_PRESBURGER_H

#include "Certify.h"
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace clang {
namespace verify {
namespace presburger {

/// Sum of Coefficients[v] * v plus Constant.
struct Linear {
  std::map<std::string, CertInt> Coefficients;
  CertInt Constant;

  static Linear constant(CertInt Value);
  static Linear variable(const std::string &Name);
  bool isConstant() const { return Coefficients.empty(); }
  CertInt coefficient(const std::string &Name) const;
  Linear operator+(const Linear &Other) const;
  Linear operator-(const Linear &Other) const;
  Linear scaled(const CertInt &Factor) const;
  /// This term with Name replaced by Value.
  Linear substituted(const std::string &Name, const Linear &Value) const;
};

struct Formula;
using FormulaPtr = std::shared_ptr<const Formula>;

struct Formula {
  enum Kind {
    True,
    False,
    /// Term <= 0.
    AtMostZero,
    /// Term == 0.
    Zero,
    /// Divisor divides Term.
    Divides,
    Not,
    And,
    Or,
    Exists,
    Forall
  };
  Kind K = True;
  Linear Term;
  CertInt Divisor;
  std::string Variable;
  std::vector<FormulaPtr> Children;
};

FormulaPtr truth(bool Value);
FormulaPtr atMostZero(Linear Term);
FormulaPtr zero(Linear Term);
FormulaPtr divides(CertInt Divisor, Linear Term);
FormulaPtr negation(FormulaPtr F);
FormulaPtr conjunction(std::vector<FormulaPtr> Children);
FormulaPtr disjunction(std::vector<FormulaPtr> Children);
FormulaPtr exists(const std::string &Variable, FormulaPtr Body);
FormulaPtr forall(const std::string &Variable, FormulaPtr Body);

/// L < R, L <= R, L == R as formulas.
FormulaPtr less(const Linear &L, const Linear &R);
FormulaPtr lessEqual(const Linear &L, const Linear &R);
FormulaPtr equal(const Linear &L, const Linear &R);

/// The truth of a closed formula, or nullopt when deciding it would build
/// more than MaxNodes nodes.
std::optional<bool> decide(const FormulaPtr &F, uint64_t MaxNodes);

} // namespace presburger
} // namespace verify
} // namespace clang

#endif
