int db(int m) {
  return 2 * m; }
int main(int n) {
  int abs = 0;
  if (n >= 0)
     abs = n;
  else
     abs = -n;
  int res = dbl(abs);
  return res;
  }
