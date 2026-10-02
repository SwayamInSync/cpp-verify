//===--- Presburger.cpp - Deciding linear integer formulas ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Presburger.h"
#include <algorithm>
#include <set>

using namespace clang;
using namespace verify;
using namespace verify::presburger;

namespace {

CertInt magnitude(const CertInt &V) { return V.isNegative() ? -V : V; }

CertInt remainder(const CertInt &A, const CertInt &B) {
  return A - B * A.truncDiv(B);
}

CertInt gcd(CertInt A, CertInt B) {
  A = magnitude(A);
  B = magnitude(B);
  while (!B.isZero()) {
    CertInt R = remainder(A, B);
    A = B;
    B = R;
  }
  return A;
}

CertInt lcm(const CertInt &A, const CertInt &B) {
  return (magnitude(A) * magnitude(B)).truncDiv(gcd(A, B));
}

/// The least nonnegative residue of V modulo a positive M.
CertInt residue(const CertInt &V, const CertInt &M) {
  return V - M * V.floorDiv(M);
}

FormulaPtr node(Formula F) { return std::make_shared<const Formula>(F); }

bool mentions(const Linear &T, const std::string &Name) {
  return T.Coefficients.count(Name) != 0;
}

/// Counts the nodes built while deciding, to stop a blowup.
struct Budget {
  uint64_t Used = 0;
  uint64_t Max = 0;
  bool spend(uint64_t Nodes) {
    Used += Nodes;
    return Used <= Max;
  }
};

uint64_t size(const FormulaPtr &F) {
  uint64_t N = 1;
  for (const FormulaPtr &Child : F->Children)
    N += size(Child);
  return N;
}

/// Negations pushed to atoms; an equality on Name becomes two bounds, and a
/// negated bound a strict one, so that every atom on Name is a bound or a
/// (negated) divisibility.
FormulaPtr normalize(const FormulaPtr &F, const std::string &Name,
                     bool Negated) {
  switch (F->K) {
  case Formula::True:
  case Formula::False:
    return truth((F->K == Formula::True) != Negated);
  case Formula::Not:
    return normalize(F->Children[0], Name, !Negated);
  case Formula::And:
  case Formula::Or: {
    std::vector<FormulaPtr> Children;
    for (const FormulaPtr &Child : F->Children)
      Children.push_back(normalize(Child, Name, Negated));
    const bool Conjunction = (F->K == Formula::And) != Negated;
    return Conjunction ? conjunction(std::move(Children))
                       : disjunction(std::move(Children));
  }
  case Formula::AtMostZero:
    // not (t <= 0) is -t + 1 <= 0.
    if (!Negated)
      return F;
    return atMostZero(F->Term.scaled(CertInt(-1)) +
                      Linear::constant(CertInt(1)));
  case Formula::Zero: {
    const Linear &T = F->Term;
    if (!mentions(T, Name))
      return Negated ? negation(F) : F;
    const Linear Minus = T.scaled(CertInt(-1));
    if (!Negated)
      return conjunction({atMostZero(T), atMostZero(Minus)});
    return disjunction({atMostZero(T + Linear::constant(CertInt(1))),
                        atMostZero(Minus + Linear::constant(CertInt(1)))});
  }
  case Formula::Divides:
    return Negated ? negation(F) : F;
  case Formula::Exists:
  case Formula::Forall:
    break;
  }
  return F;
}

/// Every atom of a normalized, quantifier-free formula.
void atoms(const FormulaPtr &F, std::vector<const Formula *> &Out) {
  switch (F->K) {
  case Formula::AtMostZero:
  case Formula::Zero:
  case Formula::Divides:
    Out.push_back(F.get());
    return;
  default:
    for (const FormulaPtr &Child : F->Children)
      atoms(Child, Out);
  }
}

/// Rebuilds F with each atom on Name replaced by Atom(atom); other atoms are
/// kept.
template <typename Fn>
FormulaPtr mapAtoms(const FormulaPtr &F, const std::string &Name, Fn Atom,
                    Budget &B) {
  if (!B.spend(1))
    return nullptr;
  switch (F->K) {
  case Formula::AtMostZero:
  case Formula::Zero:
  case Formula::Divides:
    if (!mentions(F->Term, Name))
      return F;
    return Atom(*F);
  case Formula::Not: {
    FormulaPtr Inner = mapAtoms(F->Children[0], Name, Atom, B);
    return Inner ? negation(Inner) : nullptr;
  }
  case Formula::And:
  case Formula::Or: {
    std::vector<FormulaPtr> Children;
    for (const FormulaPtr &Child : F->Children) {
      FormulaPtr Mapped = mapAtoms(Child, Name, Atom, B);
      if (!Mapped)
        return nullptr;
      Children.push_back(std::move(Mapped));
    }
    return F->K == Formula::And ? conjunction(std::move(Children))
                                : disjunction(std::move(Children));
  }
  default:
    return F;
  }
}

FormulaPtr substitute(const FormulaPtr &F, const std::string &Name,
                      const Linear &Value, Budget &B) {
  return mapAtoms(
      F, Name,
      [&](const Formula &Atom) {
        Linear T = Atom.Term.substituted(Name, Value);
        switch (Atom.K) {
        case Formula::AtMostZero:
          return atMostZero(std::move(T));
        case Formula::Zero:
          return zero(std::move(T));
        default:
          return divides(Atom.Divisor, std::move(T));
        }
      },
      B);
}

/// exists Name. F for a quantifier-free F, without Name, by Cooper's method.
FormulaPtr cooper(const std::string &Name, const FormulaPtr &Input, Budget &B) {
  FormulaPtr F = normalize(Input, Name, false);
  std::vector<const Formula *> Atoms;
  atoms(F, Atoms);
  // Scale every atom so Name's coefficient is +-Delta, then read Delta*Name
  // as Name: the result holds for Name exactly when it holds for a multiple of
  // Delta.
  CertInt Delta(1);
  for (const Formula *Atom : Atoms) {
    const CertInt C = Atom->Term.coefficient(Name);
    if (!C.isZero())
      Delta = lcm(Delta, C);
  }
  F = mapAtoms(
      F, Name,
      [&](const Formula &Atom) {
        const CertInt C = Atom.Term.coefficient(Name);
        const CertInt Factor = Delta.truncDiv(magnitude(C));
        Linear T = Atom.Term.scaled(Factor);
        T.Coefficients[Name] = C.isNegative() ? CertInt(-1) : CertInt(1);
        if (Atom.K == Formula::AtMostZero)
          return atMostZero(std::move(T));
        return divides(Atom.Divisor * Factor, std::move(T));
      },
      B);
  if (!F)
    return nullptr;
  if (CertInt(1) < Delta)
    F = conjunction({F, divides(Delta, Linear::variable(Name))});

  Atoms.clear();
  atoms(F, Atoms);
  CertInt Period(1);
  std::vector<Linear> Lower, Upper;
  auto addUnique = [](std::vector<Linear> &Terms, Linear T) {
    for (const Linear &Existing : Terms)
      if (Existing.Coefficients == T.Coefficients &&
          Existing.Constant == T.Constant)
        return;
    Terms.push_back(std::move(T));
  };
  for (const Formula *Atom : Atoms) {
    const CertInt C = Atom->Term.coefficient(Name);
    if (C.isZero())
      continue;
    if (Atom->K == Formula::Divides) {
      Period = lcm(Period, Atom->Divisor);
      continue;
    }
    // C * x + s <= 0 with C = +-1.
    Linear Rest = Atom->Term;
    Rest.Coefficients.erase(Name);
    if (C.isNegative())
      addUnique(Lower, Rest); // x >= s
    else
      addUnique(Upper, Rest.scaled(CertInt(-1))); // x <= -s
  }
  // Use the side with fewer bounds: from below, x tends to -infinity or sits
  // a little above a lower bound; symmetrically from above.
  const bool FromBelow = Lower.size() <= Upper.size();
  FormulaPtr Infinite = mapAtoms(
      F, Name,
      [&](const Formula &Atom) -> FormulaPtr {
        if (Atom.K == Formula::Divides)
          return node(Atom);
        const bool IsUpper = !Atom.Term.coefficient(Name).isNegative();
        return truth(IsUpper == FromBelow);
      },
      B);
  if (!Infinite)
    return nullptr;
  std::vector<FormulaPtr> Cases;
  const std::vector<Linear> &Bounds = FromBelow ? Lower : Upper;
  for (CertInt J(0); J < Period; J = J + CertInt(1)) {
    FormulaPtr AtInfinity = substitute(Infinite, Name, Linear::constant(J), B);
    if (!AtInfinity)
      return nullptr;
    Cases.push_back(std::move(AtInfinity));
    for (const Linear &Bound : Bounds) {
      Linear Point =
          FromBelow ? Bound + Linear::constant(J) : Bound - Linear::constant(J);
      FormulaPtr AtPoint = substitute(F, Name, Point, B);
      if (!AtPoint)
        return nullptr;
      Cases.push_back(std::move(AtPoint));
    }
    if (!B.spend(0))
      return nullptr;
  }
  return disjunction(std::move(Cases));
}

/// F without quantifiers, innermost first.
FormulaPtr eliminate(const FormulaPtr &F, Budget &B) {
  if (!B.spend(1))
    return nullptr;
  switch (F->K) {
  case Formula::Not: {
    FormulaPtr Inner = eliminate(F->Children[0], B);
    return Inner ? negation(Inner) : nullptr;
  }
  case Formula::And:
  case Formula::Or: {
    std::vector<FormulaPtr> Children;
    for (const FormulaPtr &Child : F->Children) {
      FormulaPtr Free = eliminate(Child, B);
      if (!Free)
        return nullptr;
      Children.push_back(std::move(Free));
    }
    return F->K == Formula::And ? conjunction(std::move(Children))
                                : disjunction(std::move(Children));
  }
  case Formula::Exists: {
    FormulaPtr Body = eliminate(F->Children[0], B);
    return Body ? cooper(F->Variable, Body, B) : nullptr;
  }
  case Formula::Forall: {
    FormulaPtr Body = eliminate(F->Children[0], B);
    if (!Body)
      return nullptr;
    FormulaPtr Counter = cooper(F->Variable, negation(Body), B);
    return Counter ? negation(Counter) : nullptr;
  }
  default:
    return F;
  }
}

} // namespace

Linear Linear::constant(CertInt Value) {
  Linear T;
  T.Constant = std::move(Value);
  return T;
}

Linear Linear::variable(const std::string &Name) {
  Linear T;
  T.Coefficients[Name] = CertInt(1);
  return T;
}

CertInt Linear::coefficient(const std::string &Name) const {
  auto It = Coefficients.find(Name);
  return It == Coefficients.end() ? CertInt(0) : It->second;
}

Linear Linear::operator+(const Linear &Other) const {
  Linear T = *this;
  T.Constant = T.Constant + Other.Constant;
  for (const auto &[Name, C] : Other.Coefficients) {
    CertInt Sum = T.coefficient(Name) + C;
    if (Sum.isZero())
      T.Coefficients.erase(Name);
    else
      T.Coefficients[Name] = Sum;
  }
  return T;
}

Linear Linear::operator-(const Linear &Other) const {
  return *this + Other.scaled(CertInt(-1));
}

Linear Linear::scaled(const CertInt &Factor) const {
  Linear T;
  if (Factor.isZero())
    return T;
  T.Constant = Constant * Factor;
  for (const auto &[Name, C] : Coefficients)
    T.Coefficients[Name] = C * Factor;
  return T;
}

Linear Linear::substituted(const std::string &Name, const Linear &Value) const {
  const CertInt C = coefficient(Name);
  if (C.isZero())
    return *this;
  Linear T = *this;
  T.Coefficients.erase(Name);
  return T + Value.scaled(C);
}

FormulaPtr presburger::truth(bool Value) {
  Formula F;
  F.K = Value ? Formula::True : Formula::False;
  return node(F);
}

FormulaPtr presburger::atMostZero(Linear Term) {
  if (Term.isConstant())
    return truth(!(CertInt(0) < Term.Constant));
  // sum a_i x_i <= -c with g = gcd(a_i): sum (a_i / g) x_i <= floor(-c / g).
  CertInt G(0);
  for (const auto &[Name, C] : Term.Coefficients)
    G = gcd(G, C);
  if (CertInt(1) < G) {
    for (auto &[Name, C] : Term.Coefficients)
      C = C.truncDiv(G);
    Term.Constant = -((-Term.Constant).floorDiv(G));
  }
  Formula F;
  F.K = Formula::AtMostZero;
  F.Term = std::move(Term);
  return node(F);
}

FormulaPtr presburger::zero(Linear Term) {
  if (Term.isConstant())
    return truth(Term.Constant.isZero());
  CertInt G(0);
  for (const auto &[Name, C] : Term.Coefficients)
    G = gcd(G, C);
  if (CertInt(1) < G) {
    if (!remainder(Term.Constant, G).isZero())
      return truth(false);
    for (auto &[Name, C] : Term.Coefficients)
      C = C.truncDiv(G);
    Term.Constant = Term.Constant.truncDiv(G);
  }
  Formula F;
  F.K = Formula::Zero;
  F.Term = std::move(Term);
  return node(F);
}

FormulaPtr presburger::divides(CertInt Divisor, Linear Term) {
  Divisor = magnitude(Divisor);
  if (Divisor == CertInt(1))
    return truth(true);
  // Only residues modulo the divisor matter.
  Term.Constant = residue(Term.Constant, Divisor);
  for (auto It = Term.Coefficients.begin(); It != Term.Coefficients.end();) {
    It->second = residue(It->second, Divisor);
    if (It->second.isZero())
      It = Term.Coefficients.erase(It);
    else
      ++It;
  }
  if (Term.isConstant())
    return truth(Term.Constant.isZero());
  Formula F;
  F.K = Formula::Divides;
  F.Divisor = std::move(Divisor);
  F.Term = std::move(Term);
  return node(F);
}

FormulaPtr presburger::negation(FormulaPtr F) {
  if (F->K == Formula::True || F->K == Formula::False)
    return truth(F->K == Formula::False);
  if (F->K == Formula::Not)
    return F->Children[0];
  Formula N;
  N.K = Formula::Not;
  N.Children.push_back(std::move(F));
  return node(N);
}

static FormulaPtr junction(Formula::Kind K, std::vector<FormulaPtr> Children) {
  const Formula::Kind Unit = K == Formula::And ? Formula::True : Formula::False;
  const Formula::Kind Zero = K == Formula::And ? Formula::False : Formula::True;
  Formula J;
  J.K = K;
  for (FormulaPtr &Child : Children) {
    if (Child->K == Zero)
      return truth(Zero == Formula::True);
    if (Child->K == Unit)
      continue;
    if (Child->K == K) {
      for (const FormulaPtr &Grandchild : Child->Children)
        J.Children.push_back(Grandchild);
      continue;
    }
    J.Children.push_back(std::move(Child));
  }
  if (J.Children.empty())
    return truth(Unit == Formula::True);
  if (J.Children.size() == 1)
    return J.Children.front();
  return node(J);
}

FormulaPtr presburger::conjunction(std::vector<FormulaPtr> Children) {
  return junction(Formula::And, std::move(Children));
}

FormulaPtr presburger::disjunction(std::vector<FormulaPtr> Children) {
  return junction(Formula::Or, std::move(Children));
}

FormulaPtr presburger::exists(const std::string &Variable, FormulaPtr Body) {
  Formula F;
  F.K = Formula::Exists;
  F.Variable = Variable;
  F.Children.push_back(std::move(Body));
  return node(F);
}

FormulaPtr presburger::forall(const std::string &Variable, FormulaPtr Body) {
  Formula F;
  F.K = Formula::Forall;
  F.Variable = Variable;
  F.Children.push_back(std::move(Body));
  return node(F);
}

FormulaPtr presburger::less(const Linear &L, const Linear &R) {
  return atMostZero(L - R + Linear::constant(CertInt(1)));
}

FormulaPtr presburger::lessEqual(const Linear &L, const Linear &R) {
  return atMostZero(L - R);
}

FormulaPtr presburger::equal(const Linear &L, const Linear &R) {
  return zero(L - R);
}

std::optional<bool> presburger::decide(const FormulaPtr &F, uint64_t MaxNodes) {
  Budget B;
  B.Max = MaxNodes;
  if (!B.spend(size(F)))
    return std::nullopt;
  FormulaPtr Free = eliminate(F, B);
  if (!Free || (Free->K != Formula::True && Free->K != Formula::False))
    return std::nullopt;
  return Free->K == Formula::True;
}
