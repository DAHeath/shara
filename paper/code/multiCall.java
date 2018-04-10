def dbl(int x)
  return 2 * x
def main(n)
  abs = 0
  if (n >= 0)
     abs = n
  else
     abs = -n
  res = dbl(abs)
  assert(res >= 0)
