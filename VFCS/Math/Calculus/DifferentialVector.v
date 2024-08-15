(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Differential calculus for vector or matrix-valued function
  author    : Zhengpu Shi
  date      : 2024.06

  remark    :
  1. 这是简单类型下的实现，区别于 VVF, MVF 版本
  2. 目前只实现了实数域向量值函数和矩阵值函数的求导
  
 *)

Require Export Differential.
From FinMatrix Require Import MatrixR.

Open Scope A_scope.
Open Scope vec_scope.

(* ######################################################################### *)
(** * 向量值函数的导数 *)

Definition vderiv {n} (f : R -> vec n) : R -> vec n :=
  fun t => (fun i => (fun x => f x i)' t).

(* 示例：速度矢量 v = 位置矢量 p 的导数  *)
Section example.
  (* 给定位置矢量的三个分量 *)
  Variable px py pz : R -> R.

  (* 位置矢量 *)
  Let p : R -> vec 3 := fun t => l2v [px t; py t; pz t].
  (* 速度矢量 *)
  Let v : R -> vec 3 := vderiv p.
  (* 计算其表达式 *)
  (* Eval cbv in fun t => v2l (v t). *)
  
  (* 验证度矢量的定义 *)
  Goal forall t, v t = l2v [px ' t; py ' t; pz ' t].
  Proof. intros. veq. Qed.
End example.

Lemma vderiv_const : forall n (c : vec n), vderiv (fun t => c) = fun t => vzero.
Proof.
  intros. unfold vderiv. extensionality t. extensionality i.
  rewrite Derive_const. auto.
Qed.

Lemma vderiv_scal : forall n (c : R) (u : R -> vec n),
    vderiv (fun t => c s* u t) = fun t => c s* ((vderiv u) t).
Proof.
  intros. unfold vderiv. extensionality t. extensionality i.
  replace (fun t : R => (c s* u t) i) with (fun x : R => c * (u x i)); auto.
  rewrite Derive_scal. rewrite vnth_vscal. auto.
Qed.

Lemma vderiv_scal_fun : forall n (f : R -> R) (u : R -> vec n),
    vderiv (fun t => f t s* u t) =
      (fun t => f ' t s* u t + f t s* (vderiv u) t).
Proof.
Admitted.

Lemma vderiv_add : forall n (u v : R -> vec n),
    vderiv (fun t => u t + v t) = fun t => vderiv u t + vderiv v t.
Proof.
Admitted.

Lemma vderiv_opp : forall n (u : R -> vec n),
    vderiv (fun t => - u t) = fun t => - vderiv u t.
Proof.
Admitted.

Lemma vderiv_dot : forall n (u v : R -> vec n),
    (fun t => <u t, v t>)' = fun t => (<vderiv u t, v t> + <u t, vderiv v t>)%R.
Proof.
Admitted.

Lemma vderiv_cross : forall (u v : R -> vec 3),
    vderiv (fun t => u t \x v t) = fun t => vderiv u t \x v t + u t \x vderiv v t.
Proof.
Admitted.

Lemma vderiv_comp_fun : forall {n} (u : R -> vec n) (f : R -> R),
    vderiv (fun t => u (f t)) = (fun t => (f ' t) s* vderiv u (f t))%V.
Proof.
Admitted.


(* ######################################################################### *)
(** * 矩阵值函数的导数 *)

Open Scope mat_scope.

(** 矩阵函数的导数 *)
Definition mderiv {r c} (F : R -> mat r c) : R -> mat r c :=
  fun t => (fun i j => (fun x => F x i j)' t).

(* 矩阵函数的导数的一行，等于该行的导数 *)
Lemma mrow_mderiv_eq_vderiv : forall {r c} (f : R -> mat r c) (i : fin r),
    (fun t => (mderiv f t) i) = vderiv (fun t => (f t) i).
Proof. intros. auto. Qed.

(* 矩阵函数的导数的一列，等于该列的导数 *)
Lemma mcol_mderiv_eq_vderiv : forall {r c} (f : R -> mat r c) (j : fin c),
    (fun t => mcol (mderiv f t) j) = vderiv (fun t => mcol (f t) j).
Proof. intros. auto. Qed.

(* 矩阵函数的导数等于每行的导数构成的矩阵 *)
Lemma mderiv_eq_vderiv_row : forall {r c} (f : R -> mat r c),
    mderiv f = fun t => (fun i => vderiv (fun x => f x i) t).
Proof. auto. Qed.

(* 矩阵函数的导数等于每列的导数构成的矩阵 *)
Lemma mderiv_eq_vderiv_col : forall {r c} (f : R -> mat r c),
    mderiv f = fun t => (fun i j => vderiv (fun x => mcol (f x) j) t i).
Proof. auto. Qed.


(** (A + B)' = A' + B' *)
Lemma mderiv_madd : forall {r c} (A B : R -> mat r c),
    (forall i j t, ex_derive (fun x : R => A x i j) t) ->
    (forall i j t, ex_derive (fun x : R => B x i j) t) ->
    mderiv (fun t => A t + B t) = fun t => mderiv A t + mderiv B t.
Proof.
  intros. unfold mderiv. extensionality t. extensionality i. extensionality j.
  unfold madd. unfold Matrix.madd. unfold Matrix.mmap2.
  rewrite Derive_plus; auto.
Qed.

(** (A *v a)' = A *v a' + A' *v a 矩阵值函数乘以向量值函数的求导链式法则 *)
Lemma vderiv_mmulv : forall {r c} (A : R -> mat r c) (a : R -> vec c),
    vderiv (fun t => A t *v a t) =
      fun t => (A t *v (vderiv a) t + mderiv A t *v a t)%V.
Proof.
  intros. unfold mderiv, vderiv. extensionality t.
  extensionality i.

  (* 
     步骤 1：定义函数和导数
     定义函数 F(t)=A(t)v(t)F(t)=A(t)v(t)。我们的目标是求 F(t)F(t) 的导数 F′(t)F′(t)。

     步骤 2：应用乘积法则
     由于 F(t)F(t) 是两个函数的乘积，我们可以使用乘积法则：
     F′(t)=ddt(A(t)v(t))=A′(t)v(t)+A(t)v′(t)F′(t)=dtd​(A(t)v(t))=A′(t)v(t)+A(t)v′(t)

     步骤 3：展开矩阵和向量乘法
     将 A(t)A(t) 和 v(t)v(t) 视为矩阵和向量乘积的元素展开：
     F′(t)=[∑j=1ndAij(t)dtvj(t)]+[∑k=1nAik(t)dvk(t)dt]F′(t)=[∑j=1n​dtdAij​(t)​vj​(t)]+[∑k=1n​Aik​(t)dtdvk​(t)​]

     这里，Aij(t)Aij​(t) 表示矩阵 A(t)A(t) 中第 ii 行第 jj 列的元素，vj(t)vj​(t) 是向量 v(t)v(t) 的第 jj 个元素。

     步骤 4：重新排列项
     注意到上式中的两个求和可以交换，因为它们是线性操作。这允许我们将导数项重新排列，以显示它们是如何组合的。

     步骤 5：证明等价性
     通过重新排列项，我们可以看到 F′(t)F′(t) 的表达式与我们要证明的形式相同。这完成了证明。
 *)
  (* unfold Derive. *)
  (* simpl. *)
  (* cbn. *)
  (* Check ((fun x : R => (A x *v a x) i)') t. *)
  
Admitted.
