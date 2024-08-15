Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
Require Import Psatz.
Open Scope R_scope.

Require Import functional.
Require Import complex.

(* s = c + i w *)
Definition ref (f : R->R) (s:C) (t:R) : R :=
 let (c,w) := s in
   f t * exp (-c * t) * cos (w * t).

Definition imf (f : R->R) (s:C) (t:R) : R :=
  let (c,w) := s in
    - f t * exp (-c * t) * sin (w * t).

Definition re_int f (s:C) (b:R) : R := RInt (ref f s) 0 b.
Definition im_int f (s:C) (b:R) : R := RInt (imf f s) 0 b.

Definition CRbar := (Rbar * Rbar)%type.

(* the two parts of laplace transform of f. *)
Definition re_lap f (s:C) : Rbar := Lim (re_int f s) p_infty.
Definition im_lap f (s:C) : Rbar := Lim (im_int f s) p_infty.

Definition laplace (f:R->R)(s:C) :CRbar
  := (re_lap f s, im_lap f s ).

Definition exp_f_mul (f:R->R)(a:R)(t:R):R :=
exp (a * t) * f t.

Definition lap_left (f:R->R)(s:C): Prop :=
let (c,w) := s in
continuity f /\ ex_finite_lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty.

Definition lap_right(f:R->R)(s:C): Prop :=
let (c,w) := s in
continuity f /\ ex_finite_lim (fun b => RInt (fun t => ((- f t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty.



(* 复频域位移性质 *)
Lemma frequency_shift: forall(f:R->R)(s:C)(a:R),
lap_left (exp_f_mul f a) s ->
lap_right (exp_f_mul f a) s ->
lap_left f (s - IRC a) ->
lap_right f (s - IRC a) ->
laplace (exp_f_mul f a) s = laplace f (s - IRC a).
intros.
unfold IRC.
destruct s as (c,w).
simpl.
unfold laplace.
f_equal.
unfold re_lap.
apply Lim_ext.
intro.
unfold re_int.
apply RInt_ext.
intros.
unfold ref.
unfold exp_f_mul.
rewrite Ropp_0.
rewrite Rplus_0_r.
apply Rmult_eq_compat_r.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
ring.
unfold im_lap.
apply Lim_ext.
intro.
unfold im_int.
apply RInt_ext.
intros.
unfold imf.
unfold exp_f_mul.
rewrite Ropp_0.
rewrite Rplus_0_r.
apply Rmult_eq_compat_r.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
ring.
Qed.
