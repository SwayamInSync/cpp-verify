// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=QUANT

int quant_client(int n)
  pre(n > 0 && n <= 3)
  pre(forall(i, 0, n, i >= 0))
  pre(exists(j, 0, n, j == 0))
  post(result == n)
{
  int x = 0;
  if (n > 1)
    x = 1;
  else
    x = 0;
  return n + x - x;
}

// VERIFY: Exported: lean obligation: quant_client
// QUANT: forall {{[^ ]+}} : bool
// QUANT-NEXT: bv_to_int : int
// QUANT-NEXT: 0 : bitvector32
// QUANT-NEXT: bv_to_int : int
// QUANT-NEXT: n_0 : bitvector32