int dbl(int n) {
  return 2 * n; }
int main(int n) {
  int res = 0;
  if (n >= 0)
    res = dbl(n);
  else
    res = -1 * dbl(n);
  return res; }
