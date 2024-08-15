(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Auxilary library for R in FCS
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  remark    :
  1. field失败的原因：
    a. 出现了 / , 先用 unfold Rdiv 化简。
    b. 出现了未知变元，且不是Definition定义（不能由unfold完成），先rewrite
*)

From FinMatrix Require Export RExt.

(** A simple way to solve "0 < a": let every components of "a" is positive *)
Ltac gt0 :=
  repeat
    (try
       match goal with
       (* 0 *)
       | |- 0 < ?a + ?b => apply Rplus_lt_0_compat
       | |- 0 < ?a * ?b => apply Rmult_lt_0_compat
       | |- 0 < sqrt ?a => apply sqrt_lt_R0
       | |- 0 < ?a / ?b => unfold Rdiv
       | |- 0 < / ?a => apply Rinv_0_lt_compat
       | |- 0 < ?a ^ _ => simpl
       | |- 0 < (?a)² => unfold Rsqr
       (* R0 *)
       | |- R0 < ?a + ?b => apply Rplus_lt_0_compat
       | |- R0 < ?a * ?b => apply Rmult_lt_0_compat
       | |- R0 < sqrt ?a => apply sqrt_lt_R0
       | |- R0 < ?a / ?b => unfold Rdiv
       | |- R0 < / ?a => apply Rinv_0_lt_compat
       | |- R0 < ?a ^ _ => simpl
       | |- R0 < (?a)² => unfold Rsqr
       end;
     auto with R fcs; try lra).

(* 0 <= a *)
Ltac ge0 :=
  try
    match goal with
    | |- 0 <= ?a => apply Rlt_le; gt0
    | |- R0 <= ?a => apply Rlt_le; gt0
    end.


(** a <> 0 *)
Ltac neq0 :=
  repeat match goal with
  | |- ?a /\ ?b => repeat split
  | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; gt0
  end.



(** * Expand the database of Automatic Tactics *)

(* (** autounfold with R *) *)

(* Global Hint Unfold *)
(*   Rminus        (* a - b = a + - b *) *)
(*   Rdiv          (* a / b = a * / b *) *)
(*   : R. *)

(* (** autorewrite with R *) *)

(* Global Hint Rewrite *)
(*   Ropp_0        (* - 0 = 0 *) *)
(*   Rminus_0_r    (* r - 0 = r *) *)
(*   Rplus_0_r     (* r + 0 = r *) *)
(*   Rmult_1_r     (* r * 1 = r *) *)
(*   : R. *)

(* (** auto with R *) *)

(* Global Hint Resolve *)
(*   Rplus_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *) *)
(*   Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *) *)
(*   Rinv_0_lt_compat    (* 0 < r -> 0 < / r *) *)
(*   Rlt_gt              (* r1 < r2 -> r2 > r1 *) *)
(*   Rgt_lt              (* r1 > r2 -> r2 < r1 *) *)
(*   Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *) *)
(*   PI_RGT_0            (* PI > 0 *) *)
(*   : R. *)


(** * Control Opaque / Transparent *)

(** mathmatical functions *)

(* Global Opaque *)
(*   cos *)
(*   atan *)
(*   PI *)
(*   sqrt. *)


(** * Customized Tactics *)

(* (** a + b <> 0 *) *)
(* Ltac plus_neq0 := *)
(*   match goal with *)
(*   | |- ?a + ?b <> 0 => apply Rgt_not_eq,Rlt_gt,Rplus_lt_0_compat;  *)
(*     auto with R fcs *)
(*   end. *)
  
(* (** a * b <> 0 *) *)
(* Ltac mult_neq0 := *)
(*   match goal with *)
(*   | |- ?a * ?b <> 0 => apply Rgt_not_eq,Rlt_gt;zero_le *)
(*   end. *)

(* (** a <> 0 *) *)
(* Ltac neq0 := *)
(*   repeat match goal with *)
(*   | |- ?a /\ ?b => repeat split *)
(*   | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; zero_le *)
(*   end. *)
