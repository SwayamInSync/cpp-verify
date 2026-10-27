#include "mathx.h"

// BUG is 100, or 101 for a definition that breaks its contract.
int clamp100(int x)
{
  if (x < 0)
    return 0;
  if (x > 100)
    return BUG;
  return x;
}
