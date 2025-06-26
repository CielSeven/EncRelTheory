#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "fme_def.h"

//链表的每一个节点是一个不等式
// a0+a1x1+a2x2+.... <= 0
struct InequList{
    int* coef;       //coef[0]为常数量
    struct InequList* next;
};

struct BoundPair {
    struct InequList* upper;
    struct InequList* lower;
    struct InequList* remain;
};

struct BoundPair * BP0;

struct InequList* malloc_InequList()
  /*@ Require emp
      Ensure __return != 0 && 
             undef_data_at(&(__return->coef)) *
             undef_data_at(&(__return->next))
    */;

int* malloc_coef_array(int len)
  /*@ Require emp
      Ensure exists l, __return != 0 && abs_in_int_range(len, l) && coef_array(__return, len, l)
    */;

void free_list_cell(struct InequList* p)
  /*@ With p_coef p_next
      Require data_at(&(p->coef), p_coef) *
              data_at(&(p->next), p_next)
      Ensure emp
    */;

void free_coef_array(int* c)
  /*@ With n c0
      Require coef_array(c, n, c0)
      Ensure emp
    */;

int gcd(int a, int b)
  /*@ Require 0 < a && a <= INT_MAX &&
              0 <= b && b <= INT_MAX && emp
      Ensure __return == Zgcd(a, b) && emp
    */
{
    if (b != 0) {
        return gcd(b, a % b);
    }
    else {
        return a;
    }
}

int check_add_safe(int x, int y)
  /*@ Require -INT_MAX <= x && x <= INT_MAX &&
              -INT_MAX <= y && y <= INT_MAX && emp
      Ensure ((__return == 1 && -INT_MAX <= x + y && x + y <= INT_MAX) ||
             __return == 0) && emp
    */
{
    if (x > 0) {
        return y <= 2147483647 - x;
    }
    else {
        return y >= -2147483647 - x;
    }
}

struct InequList* NilInequList()
  /*@ Require emp
      Ensure __return == 0 && emp
    */
{
    return (void *)0;
}

struct InequList* ConsInequList(int * c, struct InequList * l)
  /*@ With n c0 l0
      Require coef_array(c, n, c0) * InequList(l, n, l0)
      Ensure InequList(__return, n, cons(c0, l0))
    */
{
    struct InequList* res = malloc_InequList();
    res->coef = c;
    res->next = l;
    return res;
}

void free_InequList(struct InequList* p)
  /*@ With n l
      Require InequList(p, n, l)
      Ensure emp
    */
{
    if(p == (void *)0) return;
    if(p->coef != (void *)0) free_coef_array(p->coef);
    if(p->next != (void *)0) free_InequList(p->next);
    free_list_cell(p);
}

//删去xn相关约束，并且生成xn的upperbound list和lowerbound list,存储于BP
void eliminate(struct InequList* r, int num)
  /*@ With n l
      Require 1 <= num &&
              num < n &&
              BP0 != 0 &&
              LP_abs_in_int_range(n, l) &&
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain)) *
              InequList(r, n, l) 
      Ensure exists b up lo re,
                    eliminate_xn(Zto_nat(num-1), l, b) &&
                    form_BP(up, lo, re, b) &&
                    InequList_nth_pos(num, up) &&
                    InequList_nth_neg(num, lo) &&
                    LP_abs_in_int_range(n, up) &&
                    LP_abs_in_int_range(n, lo) &&
                    LP_abs_in_int_range(n, re) &&
                    BP0 == BP0@pre &&
                    InequList(BP0->upper, n, up) *
                    InequList(BP0->lower, n, lo) *
                    InequList(BP0->remain, n, re)
    */
{
    struct InequList* upper = NilInequList();
    struct InequList* lower = NilInequList();
    struct InequList* remain = NilInequList();
    struct InequList* cur = r;
    struct InequList* cur_next;
    /*@ upper == 0 && lower == 0 && remain == 0 */
    /*@ Inv exists l1 l2 up lo re bp,
                l == app(l1, l2) &&
                eliminate_xn(Zto_nat(num-1), l1, bp) &&
                form_BP(up, lo, re, bp) &&
                BP0 != 0 &&
                BP0 == BP0@pre &&
                1 <= num &&
                num < n &&
                num == num@pre &&
                undef_data_at(&(BP0->upper)) *
                undef_data_at(&(BP0->lower)) *
                undef_data_at(&(BP0->remain)) *
                InequList(upper, n, up) *
                InequList(lower, n, lo) *
                InequList(remain, n, re) *
                InequList(cur, n, l2)
    */
    while(cur != (void *)0){
        /*@ exists l2, InequList(cur, n, l2) && cur != 0
            which implies
            exists x l3, l2 == cons(x, l3) && coef_array(cur->coef, n, x) * InequList(cur->next, n, l3) 
        */
        cur_next = cur -> next;
        if(cur->coef[num] != 0){
            if(cur->coef[num] > 0){
                cur->next = upper;
                upper = cur;
            }
            else {
                cur->next = lower;
                lower = cur;
            }
        }
        else {
            cur -> next = remain;
            remain = cur;
        }
        cur = cur_next;
    }
    BP0->upper = upper;
    BP0->lower = lower;
    BP0->remain = remain;
}

//r1中xn系数为正，r2中xn系数为负, num = n
//r1 : a0 + a1*x1 + .. + an-1*xn-1 + an*xn <= 0
//r2 : b0 + b1*x1 + .. + bn-1*xn-1 - bn*xn <= 0
//此时an, bn 均大于0
//生成的新约束 : c0 + c1*x1 + .. + cn-1*xn-1 <= 0
int* generate_new_constr(int* r1, int* r2, int num, int cur_num)
  /*@ With c1 c2
      Require 0 <= cur_num &&
              cur_num < num + 1 &&
              num + 1 <= INT_MAX &&
              coef_Znth(cur_num, c1, 0) > 0 && coef_Znth(cur_num, c1, 0) <= INT_MAX &&
              coef_Znth(cur_num, c2, 0) < 0 && -coef_Znth(cur_num, c2, 0) <= INT_MAX &&
              coef_array(r1, num + 1, c1) *
              coef_array(r2, num + 1, c2)
      Ensure coef_array(r1, num + 1, c1) *
             coef_array(r2, num + 1, c2) *
             ((__return == 0 && emp) ||
             (__return != 0 && exists c3, 
               generate_new_constraint(Zto_nat(cur_num-1), c1, c2, c3) &&
               abs_in_int_range(num + 1, c3) &&
               coef_array(__return, num + 1, c3)))
    */
{
    int an = r1[cur_num];
    int bn = -r2[cur_num];
    int g = gcd(an, bn);
    int m1 = bn/g;
    int m2 = an/g;
    int ub1, ub2, lb1, lb2;
    ub1 = 2147483647 / m1;
    lb1 = -2147483647 / m1;
    ub2 = 2147483647 / m2;
    lb2 = -2147483647 / m2;
    int i = 0;
    /*@ Inv m1 > 0 && m2 > 0 &&
            0 <= i && i <= num + 1 &&
            ub1 == 2147483647 / m1 &&
            lb1 == -2147483647 / m1 &&
            ub2 == 2147483647 / m2 &&
            lb2 == -2147483647 / m2 &&
            in_int_range(i, m1, c1) &&
            in_int_range(i, m2, c2) &&
            r1 == r1@pre &&
            r2 == r2@pre &&
            num == num@pre &&
            cur_num == cur_num@pre &&
            coef_array(r1, num + 1, c1) *
            coef_array(r2, num + 1, c2)
    */
    for(i = 0; i <= num; i++){
        if (r1[i] < lb1 || r1[i] > ub1) {
            return (void *)0;
        }
        if (r2[i] < lb2 || r2[i] > ub2) {
            return (void *)0;
        }
    }
    int* res = malloc_coef_array(num+1);
    /*@ Inv exists c3, m1 > 0 && m2 > 0 &&
                        0 <= i &&
                        i <= num + 1 &&
                        in_int_range(num + 1, m1, c1) &&
                        in_int_range(num + 1, m2, c2) &&
                        generate_new_constraint_partial(Zto_nat(cur_num-1), i, m1, m2, c1, c2, c3) &&
                        res != 0 &&
                        r1 == r1@pre &&
                        r2 == r2@pre &&
                        num == num@pre &&
                        cur_num == cur_num@pre &&
                        abs_in_int_range(num + 1, c3) &&
                        coef_array(r1, num + 1, c1) *
                        coef_array(r2, num + 1, c2) *
                        coef_array(res, num + 1, c3)
    */
    for(i = 0; i <= num; i++){
        //ci = m1*ai + m2*bi
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (! check_add_safe(x, y)) {
            free_coef_array(res);
            return (void *)0;
        }
        res[i] = x + y;
    }
    return res;
}

// r1中所有不等式xn系数为正，r2所有不等式中xn系数为负
struct InequList* generate_new_constraint_list(struct InequList* r1, struct InequList* r2, int num, int cur_num, struct InequList* init)
  /*@ With n l1 l2 l_init
      Require n == num + 1 &&
              0 <= cur_num &&
              cur_num < n &&
              n <= INT_MAX &&
              InequList_nth_pos(cur_num, l1) &&
              InequList_nth_neg(cur_num, l2) &&
              LP_abs_in_int_range(n, l1) &&
              LP_abs_in_int_range(n, l2) &&
              LP_abs_in_int_range(n, l_init) &&
              InequList(r1, n, l1) *
              InequList(r2, n, l2) *
              InequList(init, n, l_init)
      Ensure exists l3 l4, (__return == 0 && InequList(r1, n, l1) * InequList(r2, n, l2)) ||
                           ((generate_new_constraints(Zto_nat(cur_num-1), l1, l2, l4) &&
                           l3 == app(l4, l_init) &&
                           LP_abs_in_int_range(n, l3) &&
                           InequList(r1, n, l1) *
                           InequList(r2, n, l2) *
                           InequList(__return, n, l3)))
    */
{
    struct InequList* res = init;
    struct InequList* p1 = r1;
    /*@ Inv exists l11 l12 l3 l4,
                n == num + 1 &&
                0 <= cur_num &&
                cur_num < n &&
                InequList_nth_pos(cur_num, l1) &&
                InequList_nth_neg(cur_num, l2) &&
                l1 == app(l11, l12) &&
                generate_new_constraints(Zto_nat(cur_num-1), l11, l2, l4) &&
                l3 == app(l4, l_init) &&
                LP_abs_in_int_range(n, l3) &&
                r1 == r1@pre &&
                r2 == r2@pre &&
                num == num@pre &&
                cur_num == cur_num@pre &&
                init == init@pre &&
                InequList_seg(r1, p1, n, l11) *
                InequList(p1, n, l12) *
                InequList(r2, n, l2) *
                InequList(res, n, l3)
    */
    while(p1 != (void *)0){
        /*@ exists l11 l12, p1 != 0 && InequList_seg(r1, p1, n, l11) * InequList(p1, n, l12)
            which implies
            exists x l13,
              l12 == cons(x, l13) &&
              InequList_seg(r1, p1, n, l11) *
              coef_array(p1->coef, n, x) *
              InequList(p1->next, n, l13)
        */
        struct InequList* p2 = r2;
        /*@ Inv exists l11 x1 l12 l21 l22 l3 l4,
                    n == num + 1 &&
                    0 <= cur_num &&
                    cur_num < n &&
                    InequList_nth_pos(cur_num, l1) &&
                    InequList_nth_neg(cur_num, l2) &&
                    l1 == app(l11, cons(x1, l12)) &&
                    l2 == app(l21, l22) &&
                    p1 != 0 &&
                    generate_new_constraints_partial(Zto_nat(cur_num-1), l11, x1, l21, l22, l4) &&
                    l3 == app(l4, l_init) &&
                    LP_abs_in_int_range(n, l3) &&
                    r1 == r1@pre &&
                    r2 == r2@pre &&
                    num == num@pre &&
                    cur_num == cur_num@pre &&
                    init == init@pre &&
                    InequList_seg(r1, p1, n, l11) *
                    coef_array(p1->coef, n, x1) *
                    InequList(p1->next, n, l12) *
                    InequList_seg(r2, p2, n, l21) *
                    InequList(p2, n, l22) *
                    InequList(res, n, l3)
        */
        while(p2 != (void *)0){
            /*@ exists l21 l22, p2 != 0 && InequList_seg(r2, p2, n, l21) * InequList(p2, n, l22)
                which implies
                exists x l23,
                l22 == cons(x, l23) &&
                InequList_seg(r2, p2, n, l21) *
                coef_array(p2->coef, n, x) *
                InequList(p2->next, n, l23)
            */
            int * tmp = generate_new_constr(p1->coef, p2->coef, num, cur_num);
            if (tmp == (void *)0) {
                free_InequList(res);
                return (void *)0;
            }
            res = ConsInequList(tmp, res);
            p2 = p2->next;
        }
        p1 = p1->next;
    }
    return res;
}

//消去x2,...xn,得到x1的实数域范围
//real shadow没有整数解，原问题必没有，若有整数解，原问题未必有
int real_shadow(struct InequList** pr, int n)
  /*@ With p1 l1
      Require BP0 != 0 && pr != 0 && 
              n >= 1 && n <= INT_MAX && n <= INT_MAX-1 &&
              BP0->upper == 0 &&
              BP0->lower == 0 &&
              BP0->remain == 0 &&
              LP_abs_in_int_range(n+1, l1) &&
              data_at(pr, p1) *
              InequList(p1, n + 1, l1)
      Ensure ((__return == 1 && BP0 == BP0@pre &&
              data_at(pr, p1) *
              undef_data_at(&(BP0->upper)) *
              undef_data_at(&(BP0->lower)) *
              undef_data_at(&(BP0->remain))) 
              ||
              (exists p2 l2, __return == 0 && 
                 LP_implies(l1, l2) &&
                 BP0 == BP0@pre &&
                 data_at(pr, p2) *
                 InequList(p2, n + 1, l2) *
                 undef_data_at(&(BP0->upper)) *
                 undef_data_at(&(BP0->lower)) *
                 undef_data_at(&(BP0->remain))))
    */
{
    struct InequList * r = * pr;
    int cnt = n;
    /*@ Inv exists l2,
            BP0 != 0 && BP0 == BP0@pre &&
            pr != 0 &&
            1 <= cnt &&
            cnt <= n &&
            n == n@pre &&
            pr == pr@pre &&
            LP_implies(l1, l2) &&
            LP_abs_in_int_range(n+1, l2) &&
            undef_data_at(&(BP0->upper)) *
            undef_data_at(&(BP0->lower)) *
            undef_data_at(&(BP0->remain)) *
            data_at(pr, p1) *
            InequList(r, n + 1, l2)
    */
    while(cnt >= 2){
        eliminate(r, cnt);
        if (BP0 -> remain == (void *)0 && BP0 -> upper == (void *)0) {
            free_InequList(BP0 -> lower);
            *pr = (void *)0;
            return 0;
        }
        if (BP0 -> remain == (void *)0 && BP0 -> lower == (void *)0) {
            free_InequList(BP0 -> upper);
            *pr = (void *)0;
            return 0;
        }
        r = generate_new_constraint_list(BP0->upper, BP0->lower, n, cnt, BP0->remain);
        free_InequList(BP0->upper);
        free_InequList(BP0->lower);
        if (r == (void *)0) {
            return 1;
        }
        cnt--;
    }
    * pr = r;
    return 0;
}
