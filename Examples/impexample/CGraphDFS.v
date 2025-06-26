Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

From AUXLib Require Import Idents.

From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp.

(*************************************************************************************)
(*  this file is an example of depth first search algorithm                          *)
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
Definition _xkey : var := 10022%positive.
Definition _xv : var := 10023%positive.
Definition _ykey : var := 10024%positive.
Definition _yv : var := 10025%positive.
Definition _zkey : var := 10026%positive.
Definition _zv : var := 10027%positive.
Definition _pkey : var := 10027%positive.
Definition _pv : var := 10028%positive.
Definition _qkey : var := 10029%positive.
Definition _qv : var := 10030%positive.
Definition _N : var := 10100%positive.
Definition _ret : var := 10101%positive.
Definition _vis : var := 10102%positive.


Definition _arg1 : var := 20001%positive.
Definition _arg2 : var := 20002%positive.
Definition _arg3 : var := 20003%positive.
Definition _arg4 : var := 20004%positive.

Definition _ret1 : var := 30001%positive.
Definition _ret2 : var := 30002%positive.


Module  CDFS_AdjList.

Definition _dfs_rec := 1%positive.

(*************************************************************************************)
(*  struct vertex {                                                                  *)
(*    struct edge* vedge;                                                            *)
(*    int visited; };                                                                *)
(*  struct edge {                                                                    *)
(*   struct vertex* etail;                                                           *)
(*   struct edge* next; };                                                           *)
(*************************************************************************************)

Definition f_dfs_rec : com := <{
  _x := %_arg1;
  [_x + 1] := 1;
  _e := [_x];

  While _e != ENull Do
    _v := [_e];
    _vis := [_v + 1];
    If _vis == 0 Then
        %_arg1 := _v;
        Call (_dfs_rec);
        _e := [_e + 1]
    Else
        _e := [_e + 1]
    End
  End
}>.


End  CDFS_AdjList.
