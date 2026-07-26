// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// copy only writes when n > 0, and aliases() merely *permits* dst and src to
// alias (it does not force it), so the postcondition must account for the n == 0
// case where *dst is unchanged.
void copy(int *dst, int *src, int n)
  pre(n > 0 && n <= 1 && dst != 0 && src != 0)
  aliases(dst, src)
  modifies(*dst)
  post(*dst == (n > 0 ? old(*src) : old(*dst)))
{
  if (n > 0)
    *dst = *src;
}

// VERIFY: Verified: copy