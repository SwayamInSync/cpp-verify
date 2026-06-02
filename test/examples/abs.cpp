#include <iostream>

int abs(int x)
  pre(true)
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

int main() {
  int v = abs(-7);
  std::cout << "abs(-7) = " << v << '\n';
  return 0;
}