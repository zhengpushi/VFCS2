(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Calculus examples
  author    : Zhengpu Shi
  date      : 2023.03

 *)

Require Import Calculus.
From FinMatrix Require Import MatrixR.

(** Limit of R -> R *)
Section limit_ex1.
  Open Scope R_scope.

  (* 常函数的极限 *)
  Goal Lim (fun _ => 3) 1 = 3.
  Proof. rewrite Lim_const. auto. Qed.

  (* 恒等函数的极限 *)
  Goal Lim (fun x => x) 1 = 1.
  Proof. rewrite Lim_id. auto. Qed.

  (* 数乘函数的极限 *)
  Goal Lim (fun x => 2 * x) 1 = 2.
  Proof.
    rewrite Lim_scal_l.
    (* Rbar_mult 的证明比较困难 *)
    rewrite Lim_id. unfold Rbar_mult; simpl.
    (* 使用 autorewrite 可以化简一些简单情形 *)
    ra.
  Qed.

  (* 数乘函数的极限，再复杂一些，看看 Rbar_mult 还能否自动证明 *)
  Goal Lim (fun x => x * 5) 3 = 15.
  Proof.
    rewrite Lim_scal_r. rewrite Lim_id.
    (* 找到方法了，首先计算 Rbar 上的表达式，然后 f_equal 消去 Rbar，最后是 R 上的自动化 *)
    cbv. f_equal. ra.
  Qed.
End limit_ex1.

(** Limit of R -> vec R*)
Section limit_ex2.
  Open Scope vec_scope.
  
  (* 任给三维向量 *)
  Variable v0 : R -> vec 3.
  (* 再构造复杂一点的向量 *)
  Let v1 : R -> vec 3 := fun t => 3 s* (v0 t).

  (* 计算它的导数，同时研究极限问题。这里的命题是伪造的，并不正确，只为了研究证明 *)
  Goal vderiv v1 = fun t => fun i => (fun x => 3 * x)%R t.
  Proof.
    unfold vderiv. lazy [Derive]. extensionality t. extensionality i. unfold v1.
    (* 主要关心如何手动给定函数，并证明相等 *)
    rewrite Lim_ext with (f:= fun h => ((3 s* (v0 (t+h)%R - v0 t)) i) / h).
    2:{ intros h. rewrite vscal_vadd. f_equal.
        rewrite vnth_vadd. rewrite !vnth_vscal. cbv. ring. }
  Abort.

End limit_ex2.
