// Functions the verifier cannot represent, beside ones it can, for
// per_function_errors.test.

int table[4] = {1, 2, 3, 4};

// A statement the verifier does not represent: pick is not verified, and its
// caller relies on its contract.
int pick(int x)
  cppverify::post(cppverify::result >= 1)
{
  if (x < 0) throw x;
  if (x == 0)
    return 1;
  else
    return 2;
  // An exception is not represented.
}

int uses_pick(int x)
  cppverify::post(cppverify::result >= 1)
{
  return pick(x);
}

// A contract the verifier does not represent leaves no contract to rely on.
int lookup(int i)
  cppverify::pre(0 <= i && i < 4 && table[i] > 0)
  cppverify::post(cppverify::result >= 0)
{
  return 1;
}

int uses_lookup()
  cppverify::post(cppverify::result >= 0)
{
  return lookup(1);
}

// A spec the verifier does not represent: what reaches it is not verified.
cppverify::spec int choice(int x) {
  if (x < 0) throw x;
  if (x == 0)
    return 1;
  else
    return 2;
  // An exception is not represented.
}

int uses_choice(int x)
  cppverify::post(cppverify::result == x || choice(x) > 0)
{
  return x;
}

cppverify::proof void choice_lemma(int x)
  cppverify::post(choice(x) == choice(x))
{
}

// A lemma whose body the verifier does not represent.
cppverify::proof void zero_lemma(int x)
  cppverify::post(x * 0 == 0)
{
  if (x < 0) throw x;
  // An exception is not represented.

  // (nothing else)
}

int uses_zero_lemma(int x)
  cppverify::post(cppverify::result == 0)
{
  cppverify::ghost { zero_lemma(x); }
  return 0;
}

// An uncontracted constexpr helper, lifted for its caller.
constexpr int step(int x) {
  if (x < 0) throw x;
  if (x == 0)
    return 1;
  else
    return 2;
  // An exception is not represented.
}

int uses_step(int x)
  cppverify::post(cppverify::result >= 1)
{
  return step(x);
}

// The functions the verifier represents are verified as before.
int inc(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

cppverify::spec int twice(int x) { return x + x; }

int uses_twice(int x)
  cppverify::pre(0 <= x && x < 100)
  cppverify::post(cppverify::result == twice(x))
{
  return x + x;
}
