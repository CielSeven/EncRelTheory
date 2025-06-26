#include "../verification_stdlib.h"

int add(int x, int y)
  /*@ Require
        0 <= x && x <= 100 && 
        0 <= y && y <= 100 && emp
      Ensure
        __return == x + y && emp
   */
{
  int z;
  z = x + y;
  return z;
}

int slow_add(int x, int y)
  /*@ Require
        0 <= x && x <= 100 && 
        0 <= y && y <= 100 && emp
      Ensure
        __return == x + y && emp
   */
{
  /*@ Inv
        0 <= x && x <= 100 && 
        0 <= y && y <= 200 &&
        x + y == x@pre + y@pre && emp
   */
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  return y;
}

int add1_1(int x)
/*@ Require (INT_MIN <= x) && (x < INT_MAX) && emp
    Ensure (__return == x + 1) && emp */
{
  int y;
  y = x + 1;
  return y;
}

void add1_2(int * x)
/*@ With (v: Z)
    Require (INT_MIN <= v) && (v < INT_MAX) &&
            data_at(x, int, v)
    Ensure * x == v + 1 */
{
  * x ++;
}

void add1_3(int * * x)
/*@ With (v: Z)
    Require (INT_MIN <= v) && (v < INT_MAX) &&
            * * x == v
    Ensure * * x == v + 1 */
{
  * * x = * * x + 1;
}
