void swap(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}