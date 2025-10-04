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
Definition _str : var := 10031%positive.
Definition _vnext : var := 10032%positive.
Definition _ch : var := 10033%positive.
Definition _str_j : var := 10034%positive.
Definition _vnext_j : var := 10035%positive.
Definition _vnext_i : var := 10036%positive.


Definition _arg1 : var := 20001%positive.
Definition _arg2 : var := 20002%positive.
Definition _arg3 : var := 20003%positive.
Definition _arg4 : var := 20004%positive.
Definition _arg5 : var := 20005%positive.
Definition _arg6 : var := 20006%positive.

Definition _ret1 : var := 30001%positive.
Definition _ret2 : var := 30002%positive.
Definition _ret3 : var := 30003%positive.

Module  CKMP.

Definition _inner := 1%positive.
Definition _constr := 2%positive.



(* function innerloop 
  _arg1 : the start address of the substring 
  _arg2 : the start address of the next array
  _arg3 : the char to be compared with 
  _arg4 : j 
  _ret1 : 
*)

Definition f_inner : com := <{
  _str := % _arg1;
  _vnext := % _arg2;
  _ch := % _arg3;
  _j := % _arg4;
  _str_j := [_str + _j ];
  While (  0 < _j  && _str_j != _ch )  Do
    _j := [_vnext + ( _j - 1)];
    _str_j := [_str + _j ]
  End;
  If _str_j == _ch Then
    % _ret1 := _j + 1
  Else
  % _ret1 := 0
  End
}>.

(* function innerloop 
  _arg1 : the start address of the substring 
  _arg3 : the start address of the next 
  _arg5 : the length of the substring
*)


Definition f_constr : com := <{
  _str := % _arg1;
  _vnext := % _arg2;
  _n := % _arg5;
  [_vnext + 0] := 0;
  _j := 0;
  _i := 1;
  While ( _i < _n )  Do
    _ch := [_str + _i];
    % _arg1 := _str;
    % _arg2 := _vnext;
    % _arg3 := _ch;
    % _arg4 := _j;
    Call ( _inner );
    _j := % _ret1;
    [_vnext + _i] := _j;
    _i := _i + 1
  End
}>.

End  CKMP.

