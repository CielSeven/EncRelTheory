Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

From AUXLib Require Import Idents.

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
Definition _d : var := 10012%positive.
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


Definition _arg1 : var := 20001%positive.
Definition _arg2 : var := 20002%positive.
Definition _arg3 : var := 20003%positive.
Definition _arg4 : var := 20004%positive.

Definition _ret1 : var := 30001%positive.
Definition _ret2 : var := 30002%positive.


Module  CMergeSort.

Definition _split_while := 1%positive.
Definition _merge := 2%positive.
Definition _merge_sort := 3%positive.
Definition _ins_sort := 4%positive.
Definition _lengthle := 5%positive.
Definition _gmerge_sort := 6%positive.

(* function split_rec 
  _arg1 : the start address of the list to be splited
  _arg2 : the secondary pointer address of the splited result1
  _arg3 : the secondary pointer address of the splited result2
*)
Definition f_split_while : com := <{
  _x := % _arg1;
  _p := % _arg2;
  _q := % _arg3;
  While _x != ENull Do
    _t := [_x + 1];
    _pv := [_p];
    [_x + 1] := _pv;
    [_p] := _x;
    _x := _t;
    If _x != ENull Then
      _t := [_x + 1];
      _qv := [_q];
      [_x + 1] := _qv;
      [_q] := _x;
      _x := _t
    Else
      Skip
    End
  End;
  % _arg1 := _x;
  % _arg2 := _p;
  % _arg3 := _q
}>.

(* function merge
  _arg1 : the start address of the list1
  _arg2 : the start address of the list2
  _ret1 : the start address of the result list
*)

Definition f_merge : com := <{
  _x := % _arg1;
  _y := % _arg2;
  Alloc (_r, (cons vptr nil), 1);
  _t := _r;
  _break := 0;
  While _break == 0 Do
    If _x == ENull Then
      [_t] := _y;
      _break := 1
    Else
      If _y == ENull Then
        [_t] := _x;
        _break := 1
      Else
        _a := [_x];
        _b := [_y];
        If _a < _b Then
          [_t] := _x;
          _t := _x + 1;
          _x := [_x + 1]
        Else
          [_t] := _y;
          _t := _y + 1;
          _y := [_y + 1]
        End
      End
    End
  End;
  _t := [_r];
  Free(_r);
  % _ret1 := _t
}>. 



(* function merge_sort
  _arg1 : the start address of the list to be sorted
  _ret1 : the start address of the result list
*)

Definition f_merge_sort : com := <{
  _x := % _arg1;
  Alloc (_p, (cons vint nil), 1);
  [_p] := ENull;
  Alloc (_q, (cons vint nil), 1);
  [_q] := ENull;
  % _arg1 := _x;
  % _arg2 := _p;
  % _arg3 := _q;
  Call ( _split_while );
  _p := % _arg2;
  _q := % _arg3;
  _qv := [_q];
  _pv := [_p];
  Free(_p);
  Free(_q);
  If _qv == ENull Then
    % _ret1 := _pv
  Else
    % _arg1 := _pv;
    Call ( _merge_sort );
    _pv := % _ret1;
    % _arg1 := _qv;
    Call ( _merge_sort );
    _qv := % _ret1;
    % _arg1 := _pv;
    % _arg2 := _qv;
    Call ( _merge )
  End
}>.

(* function lengthle 
  _arg1 : the start address of the list 
  _arg2 : the integer (>=0 )
  _ret1 : whether the length of the list  <= the integer 
*)

Definition f_lengthle : com := <{
  _x := % _arg1;
  _n := % _arg4;
  While ( 0 < _n && _x != 0)  Do
    _n := _n - 1;
    _x := [_x + 1]
  End;
  If _n == 0  Then
    % _ret1 := 1
  Else 
    % _ret1 := 0
  End
}>.

(* function gmerge_sort using insertionsort
  _arg1 : the start address of the list to be sorted
  _ret1 : the start address of the result list
*)

Definition f_gmerge_sort : com := <{
  _x := % _arg1;
  % _arg4 := 8;
  Call ( _lengthle );
  _n := % _ret1;
  If _n == 1 Then
    Call ( _ins_sort )
  Else
    Alloc (_p, (cons vint nil), 1);
    [_p] := ENull;
    Alloc (_q, (cons vint nil), 1);
    [_q] := ENull;
    % _arg1 := _x;
    % _arg2 := _p;
    % _arg3 := _q;
    Call ( _split_while );
    _p := % _arg2;
    _q := % _arg3;
    _qv := [_q];
    _pv := [_p];
    Free(_p);
    Free(_q);
    % _arg1 := _pv;
    Call ( _gmerge_sort );
    _pv := % _ret1;
    % _arg1 := _qv;
    Call ( _gmerge_sort );
    _qv := % _ret1;
    % _arg1 := _pv;
    % _arg2 := _qv;
    Call ( _merge )
  End
}>.

End  CMergeSort.



