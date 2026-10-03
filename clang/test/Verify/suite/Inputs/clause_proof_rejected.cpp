#include <cppverify.h>

int exec_fn(int x) post(result == x) by { contract_assert(true); } { return x; }

spec int when_block(int n) when(n > 0) by { contract_assert(true); } {
  return n;
}

spec int declared(int n) post(result >= 0) by { contract_assert(true); };
