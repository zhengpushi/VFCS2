
(* diffferential equations on function vectors. *)
Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
From Coquelicot Require Import Rcomplements Rbar Hierarchy.
From Coquelicot Require Import Compactness Lim_seq Derive.
Require Import functional.

Open Scope type_scope.

Definition RM2 := ((R * R) * (R * R)).
Definition RV2 := R * R.

(* 二阶函数向量 *)
Definition RF2 := (R->R) * (R->R).

Open Scope R_scope.

(*二阶矩阵加法*)
Definition RM2_add (a:RM2) (b:RM2) : RM2 :=
  let '((a11,a12),(a21,a22)) := a in
  let '((b11,b12),(b21,b22)) := b in
    ((a11+b11, a12+b12), (a21+b21, a22+b22)).

(*二阶向量点积*)
Definition RV2_dot (a:RV2)(b:RV2) :R :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    a1*b1 + a2*b2.

(*二维向量乘以二维函数向量*)
Definition RV2_RF2 (a:RV2)(b:RF2) :R->R :=
let (a1,a2) := a in
let (f,g) := b in
((a1 *c f) +f (a2 *c g) ).

(*二阶矩阵减法*)
Definition RM2_minus (a:RM2)(b:RM2) : RM2 :=
  let '((a11,a12),(a21,a22)) := a in
  let '((b11,b12),(b21,b22)) := b in
    ((a11-b11, a12-b12), (a21-b21, a22-b22)).

(*求二阶矩阵的行列式*)
Definition RM2_det (a:RM2):R:=
  let '((a11,a12),(a21,a22)):= a in
  a11*a22 - a12*a21.

(*常数乘以二阶矩阵*)
Definition C_RM2_mul (c:R)(a:RM2) : RM2:= 
  let '((a11,a12),(a21,a22)) := a in
    ((c*a11,c*a12),(c*a21,c*a22)).

(*常数乘以二阶向量*)
Definition C_RV2_mul (c:R)(a:RV2) : RV2:=
let(a1,a2):= a in
(c*a1, c*a2).

(*二阶矩阵乘法*)
Definition RM2_mul (a:RM2)(b:RM2) : RM2 :=
  let '(a1,a2) := a in
  let '((b11,b12),(b21,b22)) := b in
  let b1 := (b11,b21) in
  let b2 := (b12,b22) in
    (((RV2_dot a1 b1),(RV2_dot a1 b2)),
     ((RV2_dot a2 b1),(RV2_dot a2 b2))).


(*二阶函数向量作用于参数 *)
Definition RF2_app (fv:RF2) (a:R): RV2 :=
  let '(f1,f2) := fv in
    (f1 a, f2 a).
  
(*二阶矩阵乘以二阶向量 *)
Definition RMV2_cmul (a:RM2) (v:RV2) : RV2 :=
  let '(a1,a2) := a in
   (RV2_dot a1 v, RV2_dot a2 v).

(*二阶矩阵乘以二阶函数向量*)
Definition RF2_cmul (a:RM2)(v:RF2):RF2 :=
  let (a1,a2) := a in
  (RV2_RF2 a1 v , RV2_RF2 a2 v ).
  
(*
(*二阶矩阵乘以二阶函数向量 *)
Definition RF2_cmul (a:RM2)(v:RF2) (b:R) : RV2 :=
  let '(a1,a2) := a in
  let vx := RF2_app v b in
   (RV2_dot a1 vx, RV2_dot a2 vx).
*)

Definition RF2_plus(u:RF2)(v:RF2):RF2 :=
  let (u1,u2) := u in
  let (v1,v2) := v in
  (u1 +f v1, u2 +f v2).

(*二阶向量等式*)
Definition RV2_eq (a:RV2)(b:RV2) : Prop :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    a1=b1 /\ a2=b2.

(*二阶矩阵相等*)
Definition RM2_eq (a:RM2) (b:RM2) : Prop :=
  let '(a1,a2) := a in
  let '(b1,b2) := b in
   (RV2_eq a1 b1) /\ (RV2_eq a2 b2).

(* 二阶向量导函数 *)
Definition derive_RV2 (fx2:RF2): RF2 :=
  let '(f1,f2) := fx2 in
    (Derive f1 , Derive f2).

(*二阶向量相加*)
Definition RV2_add (a:RV2)(b:RV2) :RV2 :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    (a1+b1 , a2+b2).

(*二阶向量减法*)
Definition RV2_minus (a:RV2)(b:RV2) :RV2 :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    (a1-b1 , a2-b2).

(*
Open Scope type_scope.


Definition RM2 := ((R * R) * (R * R)).
Definition RV2 := R * R.

(* 二阶函数向量 *)
Definition RF2 := (R->R) * (R->R).

Open Scope R_scope.

(*二阶矩阵加法*)
Definition RM2_add (a:RM2) (b:RM2) : RM2 :=
  let '((a11,a12),(a21,a22)) := a in
  let '((b11,b12),(b21,b22)) := b in
    ((a11+b11, a12+b12), (a21+b21, a22+b22)).

(*二阶向量点积*)
Definition RV2_dot (a:RV2)(b:RV2) :R :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    a1*b1 + a2*b2.

(*二阶函数向量作用于参数 *)
Definition RF2_app (fv:RF2) (xv:RV2) : RV2 :=
  let '(f1,f2) := fv in
  let '(x1,x2) := xv in
    (f1 x1, f2 x2).
  
(*二阶矩阵乘以二阶向量 *)
Definition RMV2_cmul (a:RM2) (v:RV2) : RV2 :=
  let '(a1,a2) := a in
   (RV2_dot a1 v, RV2_dot a2 v).

(*二阶矩阵乘以二阶函数向量 *)
Definition RF2_cmul (a:RM2) (v:RF2) (xv:RV2) : RV2 :=
  let '(a1,a2) := a in
  let vx := RF2_app v xv in
   (RV2_dot a1 vx, RV2_dot a2 vx).


(*二阶向量等式*)
Definition RV2_eq (a:RV2)(b:RV2) : Prop :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    a1=b1 /\ a2=b2.


(* 二阶向量导函数 *)

Definition derive_RV2 (fx2:RF2) (xv:RV2) : RV2 :=
  let '(f1,f2) := fx2 in
  let (x1,x2) := xv in
    (Derive f1 x1, Derive f2 x2).

(*二阶向量相加*)
Definition RV2_add (a:RV2)(b:RV2) :RV2 :=
  let '(a1,a2):= a in
  let '(b1,b2):= b in
    (a1+b1 , a2+b2).

(* 二阶向量线性微分方程: X' = A X + B C  *)
Definition diff_RV2 (fx2:RF2) (a:RM2) (b:RM2) (xv:RV2) (c:RV2) : RV2 * RV2 :=
  let left  := derive_RV2 fx2 xv in
  let xv2   := RF2_app fx2 xv in 
  let ax2   := RMV2_cmul a xv2 in
  let bc2   := RMV2_cmul b c in
  let right := RV2_add ax2 bc2 in
    (left,right).

(* 二阶向量线性微分方程谓词形式: X' = A X + B C  *)
Definition diff_RV2_pred (fx2:RF2) (a:RM2) (b:RM2) (xv:RV2) (c:RV2) : Prop :=
  let (df,sum) := diff_RV2 fx2 a b xv c in
     RV2_eq df sum.
*)

