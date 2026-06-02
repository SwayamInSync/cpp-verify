void swap_bad(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
  *a = 0;
  *b = 0;
}