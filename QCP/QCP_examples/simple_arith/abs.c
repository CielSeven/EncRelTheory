#include "../verification_stdlib.h"

/*@ Extern Coq (Zabs: Z -> Z) */

int abs(int x)
  /*@ Require
        INT_MIN < x &&
        x <= INT_MAX && emp
      Ensure
        __return == Zabs(x) && emp
   */
{
  if (x < 0) {
    return -x;
  }
  else {
    return x;
  }
}
