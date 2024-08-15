(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : n-order homogeneous linear differential equation
              n阶常系数齐次线性微分方程
  author    : Zhengpu Shi
  date      : 2024.05
  
  ref       :
  1. https://en.wikipedia.org/wiki/Linear_differential_equation#Homogeneous_equation_with_constant_coefficients
  2. 高等数学学习手册，徐小湛
 *)

From FinMatrix Require Import Vector.
Require Import DEbase.

(* we prefer explicit arguments to show more informations *)
Arguments vec : clear implicits.

(** Equation: a0 y + a1 y' + a2 y'' + ... + a(n-1) y^(n-1) + y^(n) = 0 *)
Record Eqn (n : nat) := {
    a : vec R n;
  }.
Arguments Build_Eqn {n}.
Arguments a {n}.
Notation "e .a" := (a e) (at level 20, format "e .a").

(** The solution y(x) satisfy the equation *)
(* Section make_solution. *)
(*   Variable n : nat. *)
(*   Variable e : Eqn n. *)
(*   Variable y : R -> R. *)
(*   Let a' : vec R (S n) := vconsT (e.a) 1. *)
(*   Let y' : vec (R -> R) (S n) := fun i => a'.[i] c* (Derive_n y i). *)
(*   Check vsum faddR fzeroR y'. *)
(* End make_solution. *)

Definition isSolution {n} (e : Eqn n) (y : R -> R) : Prop :=
  let a' : vec R (S n) := vconsT (e.a) 1 in
  let y' : vec (R -> R) (S n) := fun i => (a'.[i] s* (Derive_n y i))%F in
  vsum fadd fzero y' = fzero.

(* The characteristic equation is:
   a0 + a1 r + a2 r^2 + ... + a(n-1) r^(n-1) + r^n = 0 *)

(** The solution r satisfy the characteristic equation *)
(* Section make_solution. *)
(*   Variable n : nat. *)
(*   Variable e : Eqn n. *)
(*   Variable r : C. *)
(*   Let a' : vec R (S n) := vconsT (e.a) 1. *)
(*   Let y' : vec C (S n) := fun i => ((R2C a'.[i]) * (Cpow r i))%C. *)
(*   Check vsum Cadd C0 y'. *)
(* End make_solution. *)

Definition isSolOfChEq {n} (e : Eqn n) (r : C) : Prop :=
  let a' : vec R (S n) := vconsT (e.a) 1 in
  let y' : vec C (S n) := fun i => ((R2C a'.[i]) * (Cpow r i))%C in
  vsum Cadd C0 y' = C0.
  

(* ======================================================================= *)
(** ** The general item when r is a single real root *)

(* If r is a single real root, output one item: C * e^{rx}. *)
Module SolR1.
  Section solution.
    (* Give an equation *)
    Variable n : nat.
    Variable e : Eqn n.

    (* Give an arbitrary constants, used for general solutions *)
    Variable c : R.

    (* Assume r is a single real root *)
    Variable r : R.
    Hypotheses Hsol : isSolOfChEq e (R2C r).

    (** The general solutions *)
    Definition y := fun x => c * exp (r * x).
    (** 1st derivative of the solution *)
    Definition dy := fun x => c * r * exp(r * x).
    (** 2st derivative of the solution *)
    Definition d2y := fun x => c * r * r * exp(r * x).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : y ' = dy.
    Proof.
      extensionality x. unfold dy,y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : dy ' = d2y.
    Proof.
      extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : y '' = d2y.
    Proof. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : isSolution e y.
    Proof.
      unfold y. revert Hsol c. revert e r. revert n.
      induction n.
      - intros. destruct e. hnf in *. cbv in *. inv Hsol. lra.
      - intros. destruct e. hnf in *.
        rewrite vsumS_tail.
        rewrite vsumS_tail in Hsol.
        specialize (IHn0 (Build_Eqn (vremoveT a0)) r).
        unfold vremoveT in *. hnf in *.
        Abort.
    (*   hnf. *)
    (*   (* eliminate derivative operations *) *)
    (*   rewrite d2_y_eq_d2y, d_y_eq_dy. *)
    (*   (* eliminate function equality *) *)
    (*   feq. *)
    (*   (* simplify *) *)
    (*   unfold d2y,dy,y,r1,r2,D in *. destruct e; simpl in *. *)
    (*   field_simplify. *)
    (*   rewrite pow2_sqrt; try lra. *)
    (* Qed. *)
  End solution.
End SolR1.
