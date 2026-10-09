// Unsigned arithmetic is defined modular wraparound in C++, so the verifier
// emits no overflow obligation for a + b. Contract arithmetic is exact, so the
// postcondition states the wraparound: verifies with no bounds.
unsigned mix(unsigned a, unsigned b)
  cppverify::post(cppverify::result == (a + b) % 4294967296)
{
  return a + b;
}
