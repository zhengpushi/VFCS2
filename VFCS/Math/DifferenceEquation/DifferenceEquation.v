(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : difference equation
  author    : Zhengpu Shi
  date      : 2021.12
  
  ref       :
  1. https://en.wikipedia.org/wiki/Recurrence_relation
  2. https://zhuanlan.zhihu.com/p/385787482
  
  remark    :
  1. a type of recurrence relation
  2. difference operator.
  
*)

Require Import FunctionalExtensionality.
Require Import Reals.
Open Scope R.

(* 序列 *)
Definition seq := nat -> R.

(* 差分方程：序列到序列的映射 *)
Definition tpDiff := seq -> seq.

(* 一阶差分 *)
Definition diff : tpDiff := 
  fun (f : seq) => 
    fun (x : nat) => f (x + 1)%nat - f x.

Notation "'Δ' f" := (diff f) (at level 30).

(* 二阶差分 *)
Notation "'Δ²' f" := (Δ (Δ f)) (at level 30).

(* 三阶差分 *)
Notation "'Δ³' f" := (Δ (Δ² f)) (at level 30).

(* 常数左乘以序列 *)
Definition seqcmull (a : R) (f : seq) : seq :=
  fun x => a * f x.
Notation "a cf* f" := (seqcmull a f) (at level 35).

(* 序列的加法 *)
Definition seqadd (f1 f2 : seq) : seq := fun x => f1 x + f2 x.
Notation "f1 f+ f2" := (seqadd f1 f2) (at level 36).

(* 常数左乘以差分 *)
Definition diffcmull (a : R) : tpDiff -> tpDiff :=
  fun d =>
    fun f x => a * ((Δ f) x).
Notation "a cd* d" := (diffcmull a d) (at level 35).

(* 差分的加法 *)
Definition diffadd (d1 d2 : tpDiff) : tpDiff :=
  fun f =>
    fun x => (d1 f) x - (d2 f) x.
Notation "d1 d+ d2" := (diffadd d1 d2) (at level 35).


(** 差分算子的性质 *)
(* 手工证明：
  Δ(au+bv)
= (a*u + b*v)(x+1) - (a*u + b*v)(x)
= (a*u)(x+1) + (b*v)(x+1) - (a*u)(x) - (b*v)(x)
= [(a*u)(x+1) - (a*u)(x)] + [(b*v)(x+1) - (b*v)(x)]
= a [u(x+1) - u(x)] + b [v(x+1) - v(x)]
= aΔu + bΔv
*)
Lemma diff_linear : forall (u v : seq) (a b : R),
  Δ ((a cf* u) f+ (b cf* v)) = (a cf* (Δ u)) f+ (b cf* (Δ v)).
Proof.
  intros.
  unfold diff, seqcmull, seqadd.
  apply functional_extensionality. intros.
  ring_simplify. ring.
Qed.
