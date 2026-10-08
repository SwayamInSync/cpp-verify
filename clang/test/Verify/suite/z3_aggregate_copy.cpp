// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int first;
  int second;
};

Pair valid_brace_initialization()
  cppverify::post(cppverify::result.first == 3)
  cppverify::post(cppverify::result.second == 4)
{
  Pair value{3, 4};
  return value;
}

Pair valid_copy_initialization(Pair source)
  cppverify::post(cppverify::result.first == source.first)
  cppverify::post(cppverify::result.second == source.second)
{
  Pair copy = source;
  return copy;
}

Pair valid_copy_assignment(Pair source)
  cppverify::post(cppverify::result.first == source.first)
  cppverify::post(cppverify::result.second == source.second)
{
  Pair copy{};
  copy = source;
  return copy;
}

Pair valid_const_copy()
  cppverify::post(cppverify::result.first == 5)
  cppverify::post(cppverify::result.second == 6)
{
  const Pair source{5, 6};
  Pair copy(source);
  return copy;
}

int valid_conditional_field(bool choose_first, Pair first, Pair second)
  cppverify::post(cppverify::result == (choose_first ? first.first : second.first))
{
  return (choose_first ? first : second).first;
}

int valid_old_conditional_field(bool choose_first, Pair first, Pair second)
  cppverify::post(cppverify::result == cppverify::old((choose_first ? first : second).first))
{
  int saved = (choose_first ? first : second).first;
  first.first = 0;
  second.first = 0;
  return saved;
}

Pair invalid_copy_claim(Pair source)
  cppverify::post(cppverify::result.first == source.second)
  cppverify::post(cppverify::result.second == source.first)
{
  Pair copy = source;
  return copy;
}

int invalid_conditional_field_alias(bool left, bool right, Pair first,
                                    Pair second)
  cppverify::post((left ? first : second).first ==
       (right ? first : second).first)
{
  return 0;
}

// VERIFY-DAG: Verified: valid_brace_initialization
// VERIFY-DAG: Verified: valid_copy_initialization
// VERIFY-DAG: Verified: valid_copy_assignment
// VERIFY-DAG: Verified: valid_const_copy
// VERIFY-DAG: Verified: valid_conditional_field
// VERIFY-DAG: Verified: valid_old_conditional_field
// VERIFY-DAG: error: verification failed: invalid_copy_claim
// VERIFY-DAG: error: verification failed: invalid_conditional_field_alias
