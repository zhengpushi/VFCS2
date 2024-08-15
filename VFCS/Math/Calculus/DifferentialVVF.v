(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Differential calculus for vector-valued function
  author    : Zhengpu Shi
  date      : 2024.06

  reference :
  1. 向量值函数的概念、性质与应用
     http://www.math.ntu.edu.tw/~hchu/Calculus/Calculus%5B104%5D-13.pdf

  remark    :
  1. 这是带有 VVF 类型的实现，提高了抽象程度，也带来了证明的复杂性
  2. 目前只实现了实数域上的向量值函数求导
 *)

Require Export Differential.
Require Export VecValFun.
From FinMatrix Require Import MatrixR.

Open Scope R.
Open Scope vec_scope.
Open Scope VecValFun_scope.


(* ######################################################################### *)
(** * 在元素为R类型上的向量值函数的导数 *)

Notation vvf := (@vvf R).
Notation vvfadd := (@vvfadd _ Rplus _).
Notation vvfopp := (@vvfopp _ Ropp _).
Notation vvfscal := (@vvfscal _ Rmult _).
Notation vvfdot := (@vvfdot _ Rplus 0 Rmult _).

Infix "+" := vvfadd : VecValFun_scope.
Notation "- f" := (vvfopp f) : VecValFun_scope.
Infix "s*" := vvfscal : VecValFun_scope.
Notation "< f , g >" := (vvfdot f g) : VecValFun_scope.
Infix "\x" := vvf3cross : VecValFun_scope.


(** 向量值函数的导数 *)
Definition vvfderiv {n} (f : vvf n) : vvf n :=
  fun t => (fun i => (fun x => f x i)' t).

(* 向量值函数的导数的一个元素 *)
Lemma vnth_vvfderiv : forall {n} (f : vvf n) (i : 'I_n),
    (fun t => (vvfderiv f t) i) = (fun t => f t i)'.
Proof. auto. Qed.

(* 示例：速度矢量 v = 位置矢量 p 的导数  *)
Section example.
  (* 给定位置矢量的三个分量 *)
  Variable px py pz : R -> R.

  (* 位置矢量 *)
  Let p : vvf 3 := fun t => l2v [px t; py t; pz t].
  (* 速度矢量 *)
  Let v : vvf 3 := vvfderiv p.
  (* 计算其表达式 *)
  (* Eval cbv in fun t => v2l (v t). *)
  
  (* 验证位置矢量和速度矢量的等式 *)
  Goal forall t, (vvfderiv p) t = l2v [px ' t; py ' t; pz ' t].
  Proof. intros. veq. Qed.
End example.

(* 向量值函数的导数性质 *)

Lemma vvfderiv_const : forall n (c : vec n), vvfderiv (fun t => c) = fun t => vzero.
Proof.
  intros. unfold vvfderiv. extensionality t. extensionality i.
  rewrite Derive_const. auto.
Qed.

Lemma vvfderiv_scal : forall n (c : R) (u : vvf n), vvfderiv (c s* u) = c s* vvfderiv u.
Proof.
  intros. unfold vvfderiv. extensionality t. extensionality i.
  replace (fun x : R => (c s* u) x i) with (fun x : R => c * (u x i)); auto.
  rewrite Derive_scal.
  unfold vvfscal. rewrite vnth_vscal. auto.
Qed.

Lemma vvfderiv_scal_fun : forall n (f : R -> R) (u : vvf n),
    vvfderiv (fun t => f ' t s* u t)%V =
      (fun t => (f ' t) s* u t)%V +
        (fun t => (f t) s* vvfderiv u t)%V.
Proof.
Admitted.

Lemma vvfderiv_add : forall n (u v : vvf n), vvfderiv (u + v) = vvfderiv u + vvfderiv v.
Proof.
Admitted.

Lemma vvfderiv_opp : forall n (u : vvf n), vvfderiv (- u) = - (vvfderiv u).
Proof.
Admitted.

Lemma vvfderiv_dot : forall n (u v : vvf n), (<u,v>)' = <vvfderiv u, v> +f <u, vvfderiv v>.
Proof.
Admitted.

Lemma vvfderiv_cross : forall (u v : vvf 3),
    vvfderiv (u \x v) = vvfderiv u \x v + u \x vvfderiv v.
Proof.
Admitted.

Lemma vvfderiv_comp_fun : forall {n} (u : vvf n) (f : R -> R),
    vvfderiv (fun t => u (f t)) = (fun t => (f ' t) s* vvfderiv u (f t))%V.
Proof.
Admitted.
