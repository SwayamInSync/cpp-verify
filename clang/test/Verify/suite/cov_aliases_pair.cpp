// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void copy(int *dst, int *src, int n)
  pre(n >= 0 && n <= 1)
  aliases(dst, src)
  modifies(*dst)
  post(*dst == old(*src))
{
  if (n > 0)
    *dst = *src;
}

// VERIFY: verified: copy