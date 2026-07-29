// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s

int reject_while_return(bool stop)
  post(result == 0 || result == 1)
{
  while (stop)
    invariant(stop)
  {
    return 1;
  }
  return 0;
}

int reject_do_return(bool stop)
  post(result == 0 || result == 1)
{
  do {
    if (stop)
      return 1;
  } while (false)
    invariant(true);
  return 0;
}

int reject_for_return(bool stop)
  post(result == 0 || result == 1)
{
  for (int index = 0; index < 1; ++index)
    invariant(index >= 0 && index <= 1)
  {
    if (stop)
      return 1;
  }
  return 0;
}

// CHECK-DAG: error: reject_while_return: return statements inside loops are unsupported
// CHECK-DAG: error: reject_do_return: return statements inside loops are unsupported
// CHECK-DAG: error: reject_for_return: return statements inside loops are unsupported
