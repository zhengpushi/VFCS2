(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector-Valued Function (VVF)
  author    : Zhengpu Shi
  date      : 2024.06
  
  reference :
  1. 向量值函数的概念、性质与应用
     http://www.math.ntu.edu.tw/~hchu/Calculus/Calculus%5B104%5D-13.pdf
  2. 标量、向量、矩阵、函数的关系
     https://blog.csdn.net/weixin_60737527/article/details/123801257
     
  remark    :
  1. 向量值函数是 A -> A^n 类型的函数
  2. `vvf tA n` is the type of vector-valued function, it is polymorphic
  3. Regarding "algebraic opertions", we only provide a limited implementation,
     that is, we assume that the elements have a field structure, such as R types.
     For future work, we will develop more detailed theory.
 *)

From FinMatrix Require Import Vector.
From FinMatrix Require MatrixR.

Declare Scope VecValFun_scope.
Delimit Scope VecValFun_scope with VVF.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VecValFun_scope.

(** The type of vector-valued function *)
Definition vvf {tA : Type} (n : nat) : Type := tA -> @vec tA n.

(** Get i-th element *)
Definition vvfnth {tA n} (f : @vvf tA n) (i : 'I_n) : tA -> tA := fun t => f t i.
Notation "f .[ i ]" := (vvfnth f i) : VecValFun_scope.
Notation "a .1" := (a.[#0]) : VecValFun_scope.
Notation "a .2" := (a.[#1]) : VecValFun_scope.
Notation "a .3" := (a.[#2]) : VecValFun_scope.
Notation "a .4" := (a.[#3]) : VecValFun_scope.

Hint Unfold vvfnth : vvf.

(** destruct a vvf to components *)
Lemma vvf_dest3 : forall {tA} (f : @vvf tA 3),
  exists a1 a2 a3 : tA -> tA, f = fun t => l2v (a1 t) [a1 t; a2 t; a3 t].
Proof.
  intros. exists (f.1),(f.2),(f.3). extensionality t. apply v2l_inj.
  rewrite v2l_l2v; auto.
Qed.

(** destruct a vvf to its elements *)
Ltac vvf2e a :=
  let a1 := fresh "a1" in
  let a2 := fresh "a2" in
  let a3 := fresh "a3" in
  let a4 := fresh "a4" in
  let Ha := fresh "Ha" in
  match type of a with
  (* | vec 1 => *)
  (*     destruct (veq_exist_1 a) as (a1,Ha); try rewrite Ha in *; *)
  (*     try clear a Ha *)
  (* | vvf 2 => *)
  (*     destruct (vvf_dest3 a) as (a1,(a2,Ha)); try rewrite Ha in *; *)
  (*     try clear a Ha *)
  | vvf 3 =>
      destruct (vvf_dest3 a) as (a1,(a2,(a3,Ha))); try rewrite Ha in *;
      try clear Ha
  (* | vec 4 => *)
  (*     destruct (veq_exist_4 a) as (a1,(a2,(a3,(a4,Ha)))); try rewrite Ha in *; *)
  (*     try clear a Ha *)
  end.


(* Algebraic operations *)
Section alg.
  Context `{HFiled : Field}.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a + -b).
  Infix "/" := Adiv : A_scope.

  Notation vadd := (@vadd _ Aadd _).
  Notation vopp := (@vopp _ Aopp _).
  Notation vscal := (@vscal _ Amul _).
  Notation vdot := (@vdot _ Aadd 0 Amul _).
  
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Notation vsub u v := (u + - v).
  Infix "-" := vsub : vec_scope.
  Infix "s*" := vscal : vec_scope.
  Notation "< u , v >" := (vdot u v) : A_scope.
  
  Notation vvf := (@vvf tA).
  
  (** VVF addition *)
  Definition vvfadd {n} (f g : vvf n) : vvf n := fun t => f t + g t.
  Infix "+" := vvfadd : VecValFun_scope.

  (** VVF opposition *)
  Definition vvfopp {n} (f : vvf n) : vvf n := fun t => - f t.
  Notation "- f" := (vvfopp f) : VecValFun_scope.

  (** VVF scaling *)
  Definition vvfscal {n} (a : tA) (f : vvf n) : vvf n := fun t => a s* f t.
  Infix "s*" := vvfscal : VecValFun_scope.
  Hint Unfold vvfscal : vvf.
  
  (** VVF dot product *)
  Definition vvfdot {n} (f g : vvf n) : tA -> tA := fun t => <f t, g t>.
  Notation "< f , g >" := (vvfdot f g) : VecValFun_scope.

End alg.

(* more operations on vvf over R type *)
Section vvf_R.
  Import MatrixR.
  
  (** VVF cross product on 3-dimensional vvf *)
  Definition vvf3cross (f g : vvf 3) : vvf 3 := fun t => v3cross (f t) (g t).
  Infix "\x" := vvf3cross : VecValFun_scope.

End vvf_R.

Hint Unfold
  vvfadd vvfopp vvfdot vvf3cross
  : vvf.
