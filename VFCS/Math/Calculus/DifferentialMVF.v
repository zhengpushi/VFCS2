(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Differential calculus for matrix-valued function
  author    : Zhengpu Shi
  date      : 2024.06

  remark    :
  1. 目前只实现了实数域上的矩阵值函数求导
  
 *)

Require Export Differential.
Require Export DifferentialVVF.
Require Export MatValFun.
From FinMatrix Require Import MatrixR.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VecValFun_scope.
Open Scope mat_scope.
Open Scope MatValFun_scope.


(* ######################################################################### *)
(** * 在元素为R类型上的矩阵值函数的导数 *)

Notation mvf := (@mvf R).
Notation smvf n := (mvf n n).
  
Notation mvfadd := (@mvfadd _ Rplus _ _).
Notation mvfopp := (@mvfopp _ Ropp _ _).
Notation mvfscal := (@mvfscal _ Rmult _ _).
Notation mvfmul := (@mvfmul _ Rplus 0 Rmult _ _ _).
Notation mvfmulv := (@mvfmulv _ Rplus 0 Rmult _ _).

Infix "+" := mvfadd : MatValFun_scope.
Notation "- f" := (vvfopp f) : MatValFun_scope.
Infix "s*" := mvfscal : MatValFun_scope.
Infix "*" := mvfmul : MatValFun_scope.
Infix "*v" := mvfmulv : MatValFun_scope.


(** 矩阵函数的导数 *)
Definition mvfderiv {r c} (F : mvf r c) : mvf r c :=
  fun t => (fun i j => (fun x => F x i j)' t).

(* 矩阵函数的导数的一个元素 *)
Lemma mnth_mvfderiv : forall {r c} (F : mvf r c) (i : 'I_r) (j : 'I_c),
    (fun t => (mvfderiv F t) i j) = (fun t => F t i j)'.
Proof. auto. Qed.

(* 矩阵函数的导数的一行，等于该行的导数 *)
Lemma mrow_mvfderiv_eq_vvfderiv : forall {r c} (f : mvf r c) (i : fin r),
    (fun t => (mvfderiv f t) i) = vvfderiv (fun t => (f t) i).
Proof. intros. auto. Qed.

(* 矩阵函数的导数的一列，等于该列的导数 *)
Lemma mcol_mvfderiv_eq_vvfderiv : forall {r c} (f : mvf r c) (j : fin c),
    (fun t => mcol (mvfderiv f t) j) = vvfderiv (fun t => mcol (f t) j).
Proof. intros. auto. Qed.

(* 矩阵函数的导数等于每行的导数构成的矩阵 *)
Lemma mvfderiv_eq_vvfderiv_row : forall {r c} (f : mvf r c),
    mvfderiv f = fun t => (fun i => vvfderiv (fun x => f x i) t).
Proof. auto. Qed.

(* 矩阵函数的导数等于每列的导数构成的矩阵 *)
Lemma mvfderiv_eq_vvfderiv_col : forall {r c} (f : mvf r c),
    mvfderiv f = fun t => (fun i j => vvfderiv (fun x => mcol (f x) j) t i).
Proof. auto. Qed.

(** (A\T)' = (A')\T *)
Lemma mvfderiv_mtrans : forall {r c} (A : mvf r c), mvfderiv (A\T) = (mvfderiv A)\T.
Proof. auto. Qed.

(** (A + B)' = A' + B' *)
Lemma mvfderiv_madd : forall {r c} (A B : mvf r c),
    (forall i j t, ex_derive (fun x : R => A x i j) t) ->
    (forall i j t, ex_derive (fun x : R => B x i j) t) ->
    mvfderiv (A + B) = mvfderiv A + mvfderiv B.
Proof.
  intros. unfold mvfderiv. extensionality t. extensionality i. extensionality j.
  unfold mvfadd. unfold Matrix.madd. unfold Matrix.mmap2.
  rewrite Derive_plus; auto.
Qed.

(** (A *v a)' = A *v a' + A' *v a 矩阵值函数乘以向量值函数的求导链式法则 *)
Lemma vvfderiv_mmulv : forall {r c} (A : mvf r c) (a : vvf c),
    vvfderiv (A *v a) = (A *v (vvfderiv a) + mvfderiv A *v a)%VVF.
Proof.
  intros. unfold mvfderiv, vvfderiv. extensionality t.
Admitted.
