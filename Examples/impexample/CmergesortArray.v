Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

From AUXLib Require Import Idents.
Require Import Coq.Lists.List.
From compcert.lib Require Import Integers.

From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp.

(*************************************************************************************)
(*  this file is an example of merge-sort algorithm                                  *)
(*                                                                                   *)
(*************************************************************************************)

Local Open Scope Z_scope.
Local Open Scope sets_scope.
Local Open Scope com_scope.
(*************************************************************************************)
(*  variables                                                                        *)
(*                                                                                   *)
(*************************************************************************************)
Definition _x : var := 10001%positive.
Definition _y : var := 10002%positive.
Definition _z : var := 10003%positive.
Definition _p : var := 10005%positive.
Definition _q : var := 10006%positive.
Definition _r : var := 10007%positive.
Definition _e : var := 10008%positive.
Definition _a : var := 10009%positive.
Definition _b : var := 10010%positive.
Definition _c : var := 10011%positive.
Definition _l : var := 10012%positive.
Definition _m : var := 10013%positive.
Definition _n : var := 10014%positive.
Definition _i : var := 10015%positive.
Definition _j : var := 10016%positive.
Definition _k : var := 10017%positive.
Definition _t : var := 10018%positive.
Definition _u : var := 10019%positive.
Definition _v : var := 10020%positive.
Definition _f : var := 10021%positive.
Definition _xnext : var := 10022%positive.
Definition _xv : var := 10023%positive.
Definition _ynext : var := 10024%positive.
Definition _yv : var := 10025%positive.
Definition _znext : var := 10026%positive.
Definition _zv : var := 10027%positive.
Definition _pnext : var := 10027%positive.
Definition _pv : var := 10028%positive.
Definition _qnext : var := 10029%positive.
Definition _qv : var := 10030%positive.
Definition _N : var := 10100%positive.
Definition _ret : var := 10101%positive.
Definition _break : var := 10102%positive.
Definition _L : var := 10103%positive.
Definition _M : var := 10104%positive.
Definition _n1 : var := 10105%positive.
Definition _n2 : var := 10106%positive.



Definition _arg1 : var := 20001%positive.
Definition _arg2 : var := 20002%positive.
Definition _arg3 : var := 20003%positive.
Definition _arg4 : var := 20004%positive.
Definition _arg5 : var := 20005%positive.
Definition _arg6 : var := 20006%positive.

Definition _ret1 : var := 30001%positive.
Definition _ret2 : var := 30002%positive.


Module  CMergeSort.

Definition _merge := 1%positive.
Definition _mergesort := 2%positive.


(* function merge
  _arg1 : the start address of the list
  _arg2 : the start index of list 1
  _arg3 : the end index of list 1
  _arg4 : the end index of list 2
*)

Definition f_merge : com := <{
  _x := %_arg1;
  _p := %_arg2;
  _q := %_arg3;
  _r := %_arg4;

  _n1 := _q - _p + 1;
  _n2 := _r - _q;

  Alloc (_L, (repeat vtype vint (Z.to_nat Int64.max_signed)), _n1);
  Alloc (_M, (repeat vtype vint (Z.to_nat Int64.max_signed)), _n2);

  _i := 0;
  _j := 0;

  While _i < _n1 Do 
    _t := [_x + _p + _i];
    [_L + _i] := _t;
    _i := _i + 1
  End;

  While _j < _n2 Do 
    _t := [_x + _q + 1 + _j];
    [_M + _j] := _t;
    _j := _j + 1
  End;

  _i := 0;
  _j := 0;
  _k := _p;

  While (_i < _n1 && _j < _n2) Do 
    _u := [_L + _i];
    _v := [_M + _j];
    If _u <= _v Then
      [_x + _k] := _u;
      _i := _i + 1
    Else
      [_x + _k] := _v;
      _j := _j + 1
    End;
    _k := _k + 1
  End;

  While _i < _n1 Do 
    _u := [_L + _i];
    [_x + _k] := _u;
    _i := _i + 1;
    _k := _k + 1
  End;

  While _j < _n2 Do 
    _v := [_M + _j];
    [_x + _k] := _v;
    _j := _j + 1;
    _k := _k + 1
  End;

  While  0 <= _i  Do
    Free(_L + _i);
    _i := _i - 1
  End;

  While  0 <= _j  Do
    Free(_M + _j);
    _j := _j - 1
  End

}>. 



(* function mergesort
  _arg1 : the start address of the list to be sorted
  _arg5 : the start index of list
  _arg6 : the end index of list
*)

Definition f_mergesort : com := <{
  _x := %_arg1;
  _l := %_arg5;
  _r := %_arg6;

  If _l < _r Then
    _m := _l + (_r - _l) ÷  2;
    %_arg5 := _l;
    %_arg6 := _m;
    Call ( _mergesort );
    %_arg5 := _m + 1;
    %_arg6 := _r;
    Call ( _mergesort );
    %_arg2 := _l;
    %_arg3 := _m;
    %_arg4 := _r;
    Call ( _merge )
  Else 
    Skip
  End
   
}>.

End  CMergeSort.



