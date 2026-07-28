struct Pair {
  int value;
};

int lean_names(Pair a, int a_value, int match, int theorem)
  post(result == a.value + a_value + match + theorem)
{
  return a.value + a_value + match + theorem;
}

Pair operator+(Pair lhs, Pair rhs)
  post(true)
{
  return lhs;
}
