// Unsigned arithmetic is defined modular wraparound in C++, so the verifier
// emits no overflow obligation: verifies with no bounds, even with --check-ub.
unsigned mix(unsigned a, unsigned b)
  post(result == a + b)
{
  return a + b;
}
