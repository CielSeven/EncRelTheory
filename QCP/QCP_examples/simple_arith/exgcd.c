#include "../verification_stdlib.h"

/*@ Extern Coq (Zgcd: Z -> Z -> Z)
               (Zmax: Z -> Z -> Z)
               (Zabs: Z -> Z)
 */

int abs(int x)
/*@ Require
      INT_MIN < x &&
      x <= INT_MAX && emp
    Ensure
      __return == Zabs(x) && emp
  */;

int exgcd(int a, int b, int *x, int *y)
/*@ Inter <= Proof
     Require 
      INT_MIN < a && a <= INT_MAX && INT_MIN < b && b <= INT_MAX && undef_data_at(x) * undef_data_at(y)
    Ensure
      __return == Zgcd(a, b) && a * (*x) + b * (*y) == Zgcd(a, b)
*/;

int exgcd(int a, int b, int *x, int *y)
/*@ Proof
    Require 
      INT_MIN < a && a <= INT_MAX && INT_MIN < b && b <= INT_MAX && undef_data_at(x) * undef_data_at(y)
    Ensure
      (__return == Zgcd(a, b) && a * (*x) + b * (*y) == Zgcd(a, b) && b == 0 && Zabs(*x) <= 1 && (*y) == 0) ||
      (__return == Zgcd(a, b) && a * (*x) + b * (*y) == Zgcd(a, b) && b != 0 && a % b == 0 && (*x) == 0 && Zabs(*y) <= 1) ||
      (__return == Zgcd(a, b) && a * (*x) + b * (*y) == Zgcd(a, b) && b != 0 && a % b != 0 && 
        Zabs(*x) <= Zabs(b) / Zgcd(a, b) && Zabs(*y) <= Zabs(a) / Zgcd(a, b))
*/
{
    if (b == 0) {
        if (a < 0) {
          *x = -1;
        } else if (a == 0) {
          *x = 0;
        } else {
          *x = 1;
        }
        *y = 0;
        return abs(a);
    }
    int g = exgcd(b, a % b, y, x);
    *y -= (a / b) * (*x);
    return g;
}