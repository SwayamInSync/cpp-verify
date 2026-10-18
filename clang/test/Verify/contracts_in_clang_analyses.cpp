// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -verify=cxx17 %s
// RUN: %clang_cc1 -std=c++98 -fverify-contracts -fno-verify -verify=cxx98 %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -analyze -analyzer-checker=core -DANALYZE -verify=analyzer %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o /dev/null -DMANGLE -verify=mangle %s

// Clang's own analyses meet the contract constructs by their meaning: a
// contract expression is never evaluated, and ghost code emits no code.

#if !defined(ANALYZE) && !defined(MANGLE)
#if __cplusplus >= 201103L
static_assert(noexcept(cppverify::exists(k, 0, 3, k == 1)), "");
void declared() noexcept(cppverify::forall(k, 0, 3, k >= 0)); // cxx17-error {{noexcept specifier argument is not a constant expression}}
#else
enum { Constant = cppverify::exists(k, 0, 3, k == 1) }; // cxx98-error {{expression is not an integral constant expression}}
#endif
#endif

// The analyzer goes on after ghost code.

int after_ghost(int x)
  cppverify::pre(x > 0)
{
  cppverify::ghost { int g = x; }
  int *p = 0;
  return *p; // analyzer-warning {{Dereference of null pointer}}
}

int after_check(int x)
  cppverify::pre(x > 0)
{
  cppverify::check(x > 0);
  int *p = 0;
  return *p; // analyzer-warning {{Dereference of null pointer}}
}

// A contract expression in a mangled name has no mangling yet.

#ifdef MANGLE
template <class T> void test(int (&)[sizeof(cppverify::exists(k, 0, 3, k == T()), T())]) {} // mangle-error {{cannot yet mangle ExistsExpr expression}}
template void test<int>(int (&)[sizeof(int)]);
#endif
