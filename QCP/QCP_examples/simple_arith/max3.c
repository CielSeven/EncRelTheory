#include "../verification_stdlib.h"

int max3(int x, int y, int z)
  /*@ Require
        INT_MIN <= x && x <= INT_MAX &&
        INT_MIN <= y && y <= INT_MAX &&
        INT_MIN <= z && z <= INT_MAX && emp
      Ensure
        __return >= x &&
        __return >= y &&
        __return >= z && emp
   */
{
  if (x < y)
    if (y < z)
      return z;
    else
      return y;
  else
    if (x < z)
      return z;
    else
      return x;
}
