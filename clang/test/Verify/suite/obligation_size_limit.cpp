// RUN: not %cpp-verify --jobs=1 --max-query-nodes=500 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LIMIT
// RUN: not %cpp-verify --jobs=1 --max-query-nodes=500 \
// RUN:   --diagnostics-format=json %s -- 2>&1 | FileCheck %s --check-prefix=JSON
// RUN: not %cpp-verify --lower-only --max-query-nodes=500 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LOWER
// RUN: %cpp-verify --help | FileCheck %s --check-prefix=HELP
// HELP: --max-query-nodes=<ulong> {{.*}}(default 4000000; 0 = no limit)
//
// The size is exact: at it the obligations are built, one below they are not.
// RUN: %cpp-verify --jobs=1 --max-query-nodes=1939 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=AT
// RUN: not %cpp-verify --jobs=1 --max-query-nodes=1938 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BELOW
//
// Built, the obligations share their terms, so at 3000 nodes they are built
// and proved; an archive record states each term in full, which takes more.
// RUN: %cpp-verify --jobs=1 --max-query-nodes=3000 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SHARED
// RUN: not %cpp-verify --jobs=1 --max-query-nodes=3000 --obligation-out=%t.cpv \
// RUN:   %s -- 2>&1 | FileCheck %s --check-prefix=ARCHIVE
//
// A spec unfolded as deep as its fuel stops at the limit: at fuel 40, fibo's
// unfolding would have about 2^40 copies of its body.
// RUN: not %cpp-verify --jobs=1 --max-query-nodes=200000 %s -- -DFUEL 2>&1 \
// RUN:   | FileCheck %s --check-prefix=FUEL
//
// The definitions of the specs a module applies count with its obligations:
// 2637 nodes here, fib's definitions at fuel 4 included.
// RUN: %cpp-verify --jobs=1 --max-query-nodes=2637 %s -- -DDEFINITIONS 2>&1 \
// RUN:   | FileCheck %s --check-prefix=DEFINITIONS-AT
// RUN: not %cpp-verify --jobs=1 --max-query-nodes=2636 %s -- -DDEFINITIONS \
// RUN:   2>&1 | FileCheck %s --check-prefix=DEFINITIONS

// Each check restates every assumption before it, sharing its terms, so the
// obligations of a function grow with its checks times the statements before
// them.
int steps(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x + 8)
{
  int y = x + 1;
  cppverify::check(y == x + 1);
  y = y + 1;
  cppverify::check(y == x + 2);
  y = y + 1;
  cppverify::check(y == x + 3);
  y = y + 1;
  cppverify::check(y == x + 4);
  y = y + 1;
  cppverify::check(y == x + 5);
  y = y + 1;
  cppverify::check(y == x + 6);
  y = y + 1;
  cppverify::check(y == x + 7);
  y = y + 1;
  cppverify::check(y == x + 8);
  return y;
}
// LIMIT: obligation_size_limit.cpp:[[@LINE-22]]:5: Unresolved: steps [backend=z3] [reason=query.size-limit] (the proof obligations would take at least 747 expression nodes, more than the limit of 500 (--max-query-nodes): each check repeats every assumption before it, so split the function or raise the limit)
// JSON: {"backend":"z3","function":"steps","message":"steps [backend=z3] [reason=query.size-limit] (the proof obligations would take at least 747 expression nodes, more than the limit of 500 (--max-query-nodes): each check repeats every assumption before it, so split the function or raise the limit)","reason":"query.size-limit","schema":"cppverify.diagnostic/1","severity":"error","source":{"column":5,"end_column":5,"end_line":[[@LINE-23]],"file":"{{.*}}obligation_size_limit.cpp","line":[[@LINE-23]]},"status":"unresolved"}
// LOWER: obligation_size_limit.cpp:[[@LINE-24]]:5: error: Z3 lowering failed: steps [backend=z3] [reason=query.size-limit] (the proof obligations would take at least 747 expression nodes, more than the limit of 500
// AT: Verified: steps [backend=z3]
// SHARED: Verified: steps [backend=z3]
// ARCHIVE: error: cannot serialize obligation: steps (its record would state more than 3000 expression nodes, the limit (--max-query-nodes))
// BELOW: Unresolved: steps [backend=z3] [reason=query.size-limit] (the proof obligations would take at least 1939 expression nodes, more than the limit of 1938 (--max-query-nodes)

// Its verdict relies on the contract of steps, which nothing establishes.
int caller(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x + 9)
{
  int y = steps(x);
  return y + 1;
}
// LIMIT: Unresolved: caller [backend=z3] [reason=callee.contract] (relies on the contract of steps, which is not established)
// JSON: {"backend":"z3","function":"caller","message":"caller [backend=z3] [reason=callee.contract] (relies on the contract of steps, which is not established)","reason":"callee.contract",
// LOWER: Lowered: caller
// AT: Verified: caller [backend=z3]
// BELOW: Unresolved: caller [backend=z3] [reason=callee.contract]

int small(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}
// LIMIT: Verified: small [backend=z3]
// LOWER: Lowered: small
// AT: Verified: small [backend=z3]
// BELOW: Verified: small [backend=z3]

#ifdef FUEL
cppverify::spec int fibo(int n)
  cppverify::decreases(n)
{
  return n <= 1 ? n : fibo(n - 1) + fibo(n - 2);
}

int unfolds(int n)
  cppverify::pre(n == 3)
  cppverify::post(cppverify::result == fibo(3))
{
  cppverify::ghost { cppverify::reveal_with_fuel(fibo, 40); }
  return 2;
}
#endif
// FUEL: Verified: steps [backend=z3]
// FUEL: Verified: spec decreases: fibo
// FUEL: obligation_size_limit.cpp:[[@LINE-10]]:5: Unresolved: unfolds [backend=z3] [reason=query.size-limit] (the facts about the specs it applies (at each application, their definitions unfolded as deep as their fuel, and their postconditions) would take at least {{[0-9]+}} expression nodes, more than the limit of 200000 (--max-query-nodes): lower the fuel cppverify::reveal_with_fuel gives, or raise the limit)

#ifdef DEFINITIONS
cppverify::spec int fib(int n)
  cppverify::decreases(n)
{
  return n <= 1 ? n : fib(n - 1) + fib(n - 2);
}

int defined(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x + 8 && fib(6) == 8)
{
  cppverify::ghost { cppverify::reveal_with_fuel(fib, 4); }
  int y = x;
  y = y + 1;
  cppverify::check(y == x + 1);
  y = y + 1;
  cppverify::check(y == x + 2);
  y = y + 1;
  cppverify::check(y == x + 3);
  y = y + 1;
  cppverify::check(y == x + 4);
  y = y + 1;
  cppverify::check(y == x + 5);
  y = y + 1;
  cppverify::check(y == x + 6);
  y = y + 1;
  cppverify::check(y == x + 7);
  y = y + 1;
  cppverify::check(y == x + 8);
  return y;
}
#endif
// DEFINITIONS-AT: Verified: defined [backend=z3]
// DEFINITIONS: Unresolved: defined [backend=z3] [reason=query.size-limit] (the proof obligations with the definitions of the specs they apply would take at least 2637 expression nodes, more than the limit of 2636 (--max-query-nodes): lower the fuel cppverify::reveal_with_fuel gives, split the function, or raise the limit)
