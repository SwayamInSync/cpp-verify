// Spec functions as Lean definitions, for lean_spec_definitions.test.

cppverify::spec int tri(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

cppverify::spec bool odd(int n);

cppverify::spec bool even(int n)
  cppverify::decreases(n, 1)
{
  return n <= 0 || odd(n - 1);
}

cppverify::spec bool odd(int n)
  cppverify::decreases(n, 0)
{
  return n > 0 && even(n - 1);
}

cppverify::spec int ack(int m, int n)
  cppverify::decreases(m, n)
{
  return m <= 0 ? n + 1 : (n <= 0 ? ack(m - 1, 1) : ack(m - 1, ack(m, n - 1)));
}

cppverify::spec int half(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0 && (n <= 1 || cppverify::result < n))
{
  return n <= 1 ? 0 : half(n - 2) + 1;
}

// Its measure falls by C++ division.
cppverify::spec int log2(int n)
  cppverify::decreases(n)
{
  return n <= 1 ? 0 : log2(n / 2) + 1;
}

// Its termination rests on the postcondition of half, which Lean does not
// know: it stays opaque.
cppverify::spec int steps(int n)
  cppverify::decreases(n)
{
  return n <= 1 ? 0 : steps(half(n)) + 1;
}

cppverify::proof void tri_nonneg(int n)
  cppverify::post(tri(n) >= 0)
{
}

cppverify::proof void tri_four()
  cppverify::post(tri(4) == 10)
{
}

cppverify::proof void even_four()
  cppverify::post(even(4) && !odd(4))
{
}

cppverify::proof void small_ack()
  cppverify::post(ack(1, 1) == 3)
{
}

cppverify::proof void log2_eight()
  cppverify::post(log2(8) == 3)
{
}

cppverify::proof void steps_one()
  cppverify::post(steps(1) == 0)
{
}

// Its call may have the measure -1 where the caller's is 0.
cppverify::spec int down(int n)
  cppverify::decreases(n)
{
  return n < 0 ? 0 : down(n - 1) + 1;
}

// It calls steps, which stays opaque: Lean accepts it once steps is.
cppverify::spec int count_steps(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : count_steps(n - 1) + steps(n);
}

cppverify::proof void down_zero()
  cppverify::post(down(0) == 1 && count_steps(0) == 0)
{
}

// A call under an existential sees its range.
cppverify::spec bool reaches(int n)
  cppverify::decreases(n)
{
  return n <= 0 || cppverify::exists(k, 0, n, reaches(k));
}

cppverify::proof void reaches_zero()
  cppverify::post(reaches(0))
{
}
