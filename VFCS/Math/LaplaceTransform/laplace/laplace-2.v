Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
Require Import Coquelicot.AutoDerive. (* auto_derive *)
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

Definition C_CRbar_mul (c:R)(a:CRbar): CRbar :=
let (a1,a2) := a in
(Rbar_mult (Finite c) a1, Rbar_mult (Finite c) a2).

Definition CRbar_plus (a:CRbar)(b:CRbar): CRbar :=
let (a1,a2) := a in
let (b1,b2) := b in
(Rbar_plus a1 b1, Rbar_plus a2 b2).

Definition S_CRbar_mul (s:C)(a:CRbar): CRbar :=
let (c,w) := s in
let (a1,a2) := a in
(Rbar_minus (Rbar_mult (Finite c) a1) (Rbar_mult (Finite w) a2),
 Rbar_plus (Rbar_mult (Finite w) a1) (Rbar_mult (Finite c) a2)).

Definition S_CRbar_minus (a:CRbar)(s:C) : CRbar :=
let (a1,a2) := a in
let (c,w) := s in
(Rbar_minus a1 (Finite c),
Rbar_minus  a2 (Finite w)).

Lemma continuity_implies_RiemannInt1: forall (f:R->R)(a b :R),
(forall x:R, continuity_pt f x)-> Riemann_integrable f a b.
intros.
elim (Rle_lt_dec a b). (* {a<=b} + {b<a} *)
  (* a <= b -> Riemann_integrable f a b *)
* intros.
  apply continuity_implies_RiemannInt.
  assumption.
  intros; apply H.
  (* b < a -> Riemann_integrable f a b *)
*  intros.
  apply RiemannInt_P1.
  apply continuity_implies_RiemannInt.
  lra.
  intros; apply H.
Qed.

(*指数函数，sin，cos函数是可微的 *)
Open Scope R_scope.
Require Import FunctionalExtensionality.
Lemma comp_f_ct_funeq : forall (f:R->R) (c:R), (fun t => f (c * t)) =
   comp (fun t => f t) (mult_real_fct c (fun t => t)).
intros.
extensionality t.
(* the tactic is similar to apply functional_extensionality. *)
unfold comp.
unfold mult_real_fct.
reflexivity.
Qed.

(* demonstration for the use of comp_f_ct_funeq. *)
Lemma comp_exp_ct_funeq : forall (c:R), (fun t => exp (c * t)) =
   comp (fun t => exp t) (mult_real_fct c (fun t => t)).
apply (comp_f_ct_funeq exp).
Qed.


Lemma derivable_pt_ct_sin: forall(c x:R), derivable_pt (fun t => sin (c * t)) x.
intros.
rewrite (comp_f_ct_funeq sin).
apply derivable_pt_comp.
* (* derivable_pt (mult_real_fct c (fun t : R => t)) x *)
  apply derivable_pt_scal.
  apply derivable_pt_id.
* (* derivable_pt (fun t : R => exp t)
     (mult_real_fct c (fun t : R => t) x)  *)
  apply derivable_pt_sin.
Qed.

Lemma ex_derive_sin: forall(c:R), derivable (fun t => sin (c * t)).
intro. unfold derivable. intro. apply derivable_pt_ct_sin.
Qed.

Lemma derivable_pt_ct_cos: forall(c x:R), derivable_pt (fun t => cos (c * t)) x.
intros.
rewrite (comp_f_ct_funeq cos).
apply derivable_pt_comp.
* apply derivable_pt_scal.
  apply derivable_pt_id.
* apply derivable_pt_cos.
Qed.

Lemma ex_derive_cos: forall(c:R), derivable (fun t => cos (c * t)).
intro. unfold derivable. intro. apply derivable_pt_ct_cos.
Qed.

Lemma derivable_pt_ct_exp: forall(c x:R), derivable_pt (fun t => exp (c * t)) x.
intros. auto_derive. trivial.
Qed.

Lemma ex_derive_exp: forall(c:R), derivable (fun t => exp (c * t)).
intro. unfold derivable. intro. apply derivable_pt_ct_exp.
Qed.

Lemma derivable_pt_exp : forall x:R, derivable_pt exp x.
intro. auto_derive. trivial.
Qed.


(*根据指数函数，sin，cos函数的可微性证明连续性 *)
Lemma continuity_exp: forall(c:R),continuity (fun t => exp (c * t)).
intros.
apply derivable_continuous.
apply ex_derive_exp.
Qed.

Lemma continuity_cos: forall(c:R),continuity (fun t => cos (c * t)).
intros.
apply derivable_continuous.
apply ex_derive_cos.
Qed.

Lemma continuity_sin: forall(c:R),continuity (fun t => sin (c * t)).
intros.
apply derivable_continuous.
apply ex_derive_sin.
Qed.

Lemma ex_finite_ex_lim (f:R->R)(x:Rbar):
ex_finite_lim f x -> ex_lim f x.
intros.
apply ex_finite_lim_correct.
apply H.
Qed.

Lemma ex_finite_lim_scal_l: forall(f : R -> R) (a : R) (x : Rbar),
  ex_finite_lim f x -> ex_finite_lim (fun y => (a * f y)%R) x.
intros.
unfold ex_finite_lim.
unfold ex_finite_lim in H.
elim H.
intros.
exists (a * x0)%R.
apply (is_lim_scal_l f a x x0).
assumption.
Qed.

Lemma ex_finite_plus1: forall(a:Rbar)(b:Rbar),
is_finite a ->
is_finite b ->
ex_Rbar_plus a b.
intros.
rewrite is_finite_correct in H.
rewrite is_finite_correct in H0.
elim H.
elim H0.
intros.
rewrite H1.
rewrite H2.
reflexivity.
Qed.


Lemma ex_finite_plus: forall(f:R->R)(g:R->R)(x:Rbar),
ex_finite_lim f x ->
ex_finite_lim g x ->
ex_Rbar_plus (Lim f x) (Lim g x).
intros.
apply ex_finite_plus1.
apply ex_finite_lim_correct.
apply H.
apply ex_finite_lim_correct.
apply H0.
Qed.


Lemma ex_finite_lim_opp_pre: forall(f:R->R),
(fun t:R => (- f t)%R) = (fun t:R => ((-1) * (f t))%R).
intro.
apply fun_eq.
intro.
ring.
Qed.

Lemma ex_finite_lim_opp: forall(f:R->R)(x:Rbar),
  ex_finite_lim f x -> ex_finite_lim (fun y => (- f y)%R) x.
intros.
rewrite ex_finite_lim_opp_pre.
apply ex_finite_lim_scal_l.
apply H.
Qed.


Lemma ex_finite_minus: forall(f:R->R)(g:R->R)(x:Rbar),
ex_finite_lim f x ->
ex_finite_lim g x ->
ex_Rbar_minus (Lim f x) (Lim g x).
intros.
unfold ex_Rbar_minus.
rewrite <- Lim_opp.
apply ex_finite_plus.
apply H.
apply ex_finite_lim_opp.
apply H0.
Qed.

(* The following is the definition of the existence of several functional limits *)
Definition lap_left (f:R->R)(s:C): Prop :=
let (c,w) := s in
continuity f /\ ex_finite_lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty.

Definition lap_right(f:R->R)(s:C): Prop :=
let (c,w) := s in
continuity f /\ ex_finite_lim (fun b => RInt (fun t => ((- f t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty.


Lemma lap_c_left_pre: forall(f:R->R)(c:R)(w:R)(m:R),
(fun b:R => RInt (fun t:R => (((m *c f) t) * (exp (- c * t)) * (cos (w * t)) )%R) 0 b) = 
(fun b:R => (m * (RInt (fun t:R => ((f t) * (exp (- c * t)) * (cos (w * t)) )%R) 0 b))%R).
intros.
apply fun_eq.
intro.
rewrite <- ? RInt_scal.
apply RInt_ext.
intros.
rewrite ? fconst_ok.
ring.
Qed.


Lemma lap_c_left: forall(f:R->R)(s:C)(m:R),
lap_left f s -> lap_left (m *c f) s.
intros.
unfold lap_left.
destruct s as (c,w).
split.
apply continuity_scal.
elim H.
intros.
apply H0.
rewrite lap_c_left_pre.
apply ex_finite_lim_scal_l.
elim H.
intros.
apply H1.
Qed.


Lemma lap_c_right_pre: forall(f:R->R)(c:R)(w:R)(m:R),
(fun b:R => RInt (fun t:R => ((- (m *c f) t) * (exp (- c * t)) * (sin (w * t)) )%R) 0 b) = 
(fun b:R => (m * (RInt (fun t:R => ((- f t) * (exp (- c * t)) * (sin (w * t)) )%R) 0 b))%R).
intros.
apply fun_eq.
intro.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
rewrite fconst_ok.
ring.
Qed.


Lemma lap_c_right: forall(f:R->R)(s:C)(m:R),
lap_right f s -> lap_right (m *c f) s.
intros.
unfold lap_right.
destruct s as (c,w).
split.
apply continuity_scal.
elim H.
intros.
apply H0.
rewrite lap_c_right_pre.
apply ex_finite_lim_scal_l.
elim H.
intros.
apply H1.
Qed.


(* Laplace (c * f) = c * Laplace(f) *)
Lemma const_lap : forall(f:R->R)(s:C)(m:R),
lap_left f s ->
lap_right f s ->
laplace (m *c f) s = C_CRbar_mul m (laplace f s).
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
unfold re_int.
rewrite <- Lim_scal_l.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold ref.
destruct s as (c,w).
rewrite fconst_ok.
ring.
unfold im_lap.
unfold im_int.
rewrite <- Lim_scal_l.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold imf.
destruct s as (c,w).
rewrite fconst_ok.
ring.
Qed.


(*Laplace (f + g) = (Laplace f) + (Laplace g)*)
Lemma lap_plus: forall(u:R->R)(v:R->R)(s:C),
lap_left u s ->
lap_left v s ->
lap_right u s ->
lap_right v s ->
 laplace (u +f v) s= CRbar_plus (laplace u s) (laplace v s) .
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
unfold re_int.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref.
destruct s as (c,w).
rewrite fplus_ok.
ring.
unfold ref.
destruct s as (c,w).
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
apply H3.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold ref.
destruct s as (c,w).
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H0.
intros.
apply H3.
apply continuity_exp.
apply continuity_cos.
apply ex_finite_ex_lim.
unfold ref.
destruct s as (c,w).
elim H.
intros.
apply H4.
apply ex_finite_ex_lim.
unfold ref.
destruct s as (c,w).
elim H0.
intros.
apply H4.
unfold ref.
destruct s as (c,w).
apply ex_finite_plus.
elim H.
intros.
apply H4.
elim H0.
intros.
apply H4.
(*im_lap*)
unfold im_lap.
unfold im_int.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold imf.
destruct s as (c,w).
rewrite fplus_ok.
ring.
unfold imf.
destruct s as (c,w).
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
elim H.
intros.
apply H3.
apply continuity_exp.
apply continuity_sin.
unfold imf.
destruct s as (c,w).
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
elim H0.
intros.
apply H3.
apply continuity_exp.
apply continuity_sin.
unfold imf.
destruct s as (c,w).
apply ex_finite_ex_lim.
elim H1.
intros.
apply H4.
unfold imf.
destruct s as (c,w).
apply ex_finite_ex_lim.
elim H2.
intros.
apply H4.
apply ex_finite_plus.
unfold imf.
destruct s as (c,w).
elim H1.
intros.
apply H4.
unfold imf.
destruct s as (c,w).
elim H2.
intros.
apply H4.
Qed.

(*两个函数是相等的，那么他们的拉普拉斯变换也是相等的*)
Lemma laplace_ext: forall(f:R->R)(g:R->R)(s:C),
lap_left f s ->
lap_left g s ->
lap_right f s ->
lap_right g s ->
(forall y,f y = g y) -> laplace f s = laplace g s.
intros.
unfold laplace.
f_equal.
unfold re_lap.
apply Lim_ext.
intro.
unfold re_int.
apply RInt_ext.
intros.
unfold ref.
destruct s as (c,w).
apply Rmult_eq_compat_r.
apply Rmult_eq_compat_r.
apply sym_eq.
apply H3.
unfold im_lap.
apply Lim_ext.
intro.
unfold im_int.
apply RInt_ext.
intros.
unfold imf.
destruct s as (c,w).
apply Rmult_eq_compat_r.
apply Rmult_eq_compat_r.
apply Ropp_eq_compat.
apply sym_eq.
apply H3.
Qed.


(* The first method to prove the line property *)
Lemma lap_line: forall(u:R->R)(v:R->R)(s:C)(m:R)(n:R),
lap_left u s ->
lap_left v s ->
lap_right u s ->
lap_right v s ->
laplace (m *c u +f n *c v) s = CRbar_plus (C_CRbar_mul m (laplace u s)) (C_CRbar_mul n (laplace v s)).
intros.
rewrite <- ? const_lap.
rewrite <- lap_plus.
tauto.
apply lap_c_left.
apply H.
apply lap_c_left.
apply H0.
apply lap_c_right.
apply H1.
apply lap_c_right.
apply H2.
apply H0.
apply H2.
apply H.
apply H1.
Qed.

(*
(*上面是证明线性性质的第一种方法，将线性性质分为三个小引理。这是第二种证明方式，整个进行证明*)
(* The second method to prove line property*)
Lemma lap_line1: forall(u:R->R)(v:R->R)(s:C)(m:R)(n:R),
lap_left u s ->
lap_left v s ->
lap_right u s ->
lap_right v s ->
laplace (m *c u +f n *c v) s =CRbar_plus (C_CRbar_mul m (laplace u s)) (C_CRbar_mul n (laplace v s)).
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
unfold re_int.
rewrite <- ? Lim_scal_l.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref.
destruct s as (c,w).
rewrite fplus_ok.
rewrite ? fconst_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
unfold ref.
destruct s as (c,w).
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
apply H3.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
unfold ref.
destruct s as (c,w).
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H0.
intros.
apply H3.
apply continuity_exp.
apply continuity_cos.
apply ex_lim_scal_l.
unfold ref.
destruct s as (c,w).
elim H.
intros.
apply ex_finite_ex_lim.
apply H4.
apply ex_lim_scal_l.
unfold ref.
destruct s as (c,w).
apply ex_finite_ex_lim.
elim H0.
intros.
apply H4.
apply ex_finite_plus.
apply ex_finite_lim_scal_l.
unfold ref.
destruct s as (c,w).
elim H.
intros.
apply H4.
apply ex_finite_lim_scal_l.
unfold ref.
destruct s as (c,w).
elim H0.
intros.
apply H4.
(*im_lap*)
unfold im_lap.
unfold im_int.
rewrite <- ? Lim_scal_l.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold imf.
destruct s as (c,w).
rewrite fplus_ok.
rewrite ? fconst_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
unfold imf.
destruct s as (c,w).
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
elim H.
intros.
apply H3.
apply continuity_exp.
apply continuity_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
unfold imf.
destruct s as (c,w).
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
elim H0.
intros.
apply H3.
apply continuity_exp.
apply continuity_sin.
apply ex_lim_scal_l.
apply ex_finite_ex_lim.
unfold imf.
destruct s as (c,w).
elim H1.
intros.
apply H4.
apply ex_lim_scal_l.
unfold imf.
destruct s as (c,w).
apply ex_finite_ex_lim.
elim H2.
intros.
apply H4.
apply ex_finite_plus.
apply ex_finite_lim_scal_l.
unfold imf.
destruct s as (c,w).
elim H1.
intros.
apply H4.
apply ex_finite_lim_scal_l.
unfold imf.
destruct s as (c,w).
elim H2.
intros.
apply H4.
Qed.
*)
Definition exp_f_mul (f:R->R)(a:R)(t:R):R :=
exp (a * t) * f t.

Open Scope C_scope.

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


(*两个函数的积的导数*)
Lemma Derive_mult1 (f g : R -> R) :
  derivable f  -> derivable g
    -> Derive (fun x => (f x * g x)%R)  = (Derive f)  *f g  +f  f  *f  Derive g.
intros.
apply fun_eq.
intros.
apply Derive_mult.
apply ex_derive_Reals_1.
apply H.
apply ex_derive_Reals_1.
apply H0.
Qed.

(*
(*分部积分的形式化,f和g都是可导的，而且导函数都是连续的*)
Axiom RInt_by_parts : forall(f:R->R)(g:R->R),
derivable f  ->
derivable g  ->
continuity (Derive f) ->
continuity (Derive g) ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty = Rbar_minus
(Rbar_minus (Lim (f *f g ) p_infty) (Lim (fun b => RInt (fun t:R => ((f t)*(Derive g t ))%R) 0 b) p_infty) )
(Finite ((f *f g) 0%R)).
*)
Require Import mathcomp.ssreflect.ssreflect.
From Coquelicot Require Import Rcomplements Rbar Hierarchy.
From Coquelicot Require Import Compactness Lim_seq.
(* equivalence between Standard lib continous and Coquelicot continous. *)


(* Coquelicot.Hierarchy
Lemma continuity_pt_filterlim : ∀ (f : R → R) (x : R),
  continuity_pt f x ↔ filterlim f (locally x) (locally (f x)). *)

(* equivalence between standard lib continuity_pt and coquelicot continuous. *)

Lemma continuity_equiv_continuous : forall (f : R -> R) (x : R),
  continuity_pt f x <-> continuous f x.
intros f x.
unfold continuous.
rewrite continuity_pt_filterlim.
tauto.
Qed.


Require Import Coquelicot.RInt_analysis.

Lemma RInt_Derive1: forall(f:R->R)(a b : R),
(forall x, Rmin a b <= x <= Rmax a b -> derivable_pt f x) ->
(forall x, Rmin a b <= x <= Rmax a b -> continuity_pt (Derive f) x) ->
RInt (Derive f) a b = (f b - f a)%R.
intros.
apply RInt_Derive. 
intros.
apply ex_derive_Reals_1.
apply H.
apply H1.
intros.
apply continuity_equiv_continuous.
apply H0.
apply H1.
Qed.


Lemma l3: forall(f:R->R)(g:R->R),
derivable (f *f g) ->
continuity (Derive (f *f g))->
(fun b => RInt (fun t:R => (Derive (f *f g) t)%R) 0 b)=
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
apply fun_eq.
intro.
rewrite RInt_Derive1.
tauto.
intros.
apply H.
intros.
apply H0.
Qed.

(* 2017/7/20*)
Lemma l3_modify: forall(f:R->R)(g:R->R),
derivable f ->
derivable g ->
continuity (Derive f) -> 
continuity (Derive g) ->
(fun b => RInt (fun t:R => (Derive (f *f g) t)%R) 0 b)=
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
apply fun_eq.
intro.
rewrite RInt_Derive1.
tauto.
intros.
apply derivable_pt_mult.
apply H.
apply H0.
intros.
rewrite Derive_mult1.
apply continuity_plus.
apply continuity_mult.
apply H1.
apply derivable_continuous.
apply H0.
apply continuity_mult.
apply derivable_continuous.
apply H.
apply H2.
apply H.
apply H0.
Qed.



Lemma l3_1: forall(f:R->R)(g:R->R),
derivable (f *f g) ->
continuity (Derive (f *f g))->
RInt (fun t:R => (Derive (f *f g) t)%R) 0 =
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
apply fun_eq.
intros.
rewrite RInt_Derive1.
tauto.
intros.
apply H.
intros.
apply H0.
Qed.

Lemma RInt_by_parts1: forall(f:R->R)(g:R->R),
derivable f ->
derivable g ->
continuity (Derive f) ->
continuity (Derive g) ->
ex_finite_lim (RInt (fun t:R => (Derive (f *f g) t)%R) 0) p_infty ->
ex_finite_lim (RInt (fun t:R => ((f t)*(Derive g t))%R) 0) p_infty ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty  = Rbar_minus
(Lim (fun b => RInt (fun t:R => (Derive (f *f g) t)%R ) 0 b) p_infty)
(Lim (fun b => RInt (fun t:R => ((f t) * (Derive g t))%R ) 0 b) p_infty).
intros.
rewrite <- Lim_minus.
apply Lim_ext.
intro.
rewrite <- RInt_minus.
apply RInt_ext.
intros.
unfold fmul.
rewrite Derive_mult.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
ring.
apply ex_derive_Reals_1.
apply H.
apply ex_derive_Reals_1.
apply H0.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold fmul.
rewrite Derive_mult1.
apply continuity_pt_plus.
apply continuity_pt_mult.
apply H1.
apply derivable_continuous_pt.
apply H0.
apply continuity_pt_mult.
apply derivable_continuous_pt.
apply H.
apply H2.
apply H.
apply H0.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply derivable_continuous_pt.
apply H.
apply H2.
apply ex_finite_ex_lim.
apply H3.
apply ex_finite_ex_lim.
apply H4.
apply ex_finite_minus.
apply H3.
apply H4.
Qed.

Lemma RInt_by_parts: forall(f:R->R)(g:R->R),
derivable f ->
derivable g ->
continuity (Derive f) ->
continuity (Derive g) ->
ex_finite_lim (RInt (fun t:R => (Derive (f *f g) t)%R) 0) p_infty ->
ex_finite_lim (RInt (fun t:R => ((f t)*(Derive g t))%R) 0) p_infty ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty  = Rbar_minus
(Lim (fun b => ((f *f g) b - (f *f g) 0)%R) p_infty)
(Lim (fun b => RInt (fun t:R => ((f t) * (Derive g t))%R ) 0 b) p_infty).
intros.
rewrite <- l3_modify.
apply RInt_by_parts1.
apply H.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H.
apply H0.
apply H1.
apply H2.
Qed.


(*定义两个谓词，用来表示 下面这个函数在正无穷大出的极限值*)
Definition f_lim_0_cos (f:R->R)(s:C):R->R :=
let (c,w) := s in
(f *f (fun t:R => ((exp (- c * t)) * (cos (w * t)))%R)).

Definition f_lim_0_sin (f:R->R)(s:C):R->R:=
let (c,w) := s in
((fun x:R => (- f x)%R) *f (fun t:R => ((exp (- c * t)) * (sin (w * t)))%R) ).

(*分部积分的定义有两个函数f和g的乘积，后面证明中出现三个函数的乘积，需要将函数变形为右结合*)
Lemma RInt_by_parts_e1: forall(f:R->R)(c:R)(w:R),
(fun b:R => RInt (fun t:R => ((Derive f t) * (exp (- c * t)) * (cos (w * t)))%R) 0 b) = 
(fun b:R => RInt (fun t:R => ((Derive f t) * ((exp (- c * t)) * (cos (w * t))))%R) 0 b).
intros.
apply fun_eq.
intro.
apply RInt_ext.
intros.
ring.
Qed.

(*将函数变为右结合，便于后续的证明*)
Lemma RInt_by_parts_e2: forall(f:R->R)(c:R)(w:R),
(fun t:R => ((- Derive f t) * (exp (- c * t)) * (sin (w * t)))%R) = 
(fun t:R => ((Derive (fun x:R => (- f x)%R ) t) * ((exp (- c * t)) * (sin (w * t))))%R).
intros.
extensionality t.
rewrite <- Derive_opp.
ring.
Qed.

(*下面几个小引理是对Coquelicot库的扩充基础引理,包括之前的引理ex_finite_lim,ex_finite_plus等*)
Lemma Rbar_minus_0_r: forall (a:Rbar),
Rbar_minus (Finite 0) a = Rbar_opp a.
intro.
unfold Rbar_minus.
apply Rbar_plus_0_l.
Qed.

Lemma Rbar_opp_0: Rbar_opp (Finite 0) = (Finite 0).
unfold Rbar_opp.
rewrite Rbar_finite_eq.
apply Ropp_0.
Qed.

Lemma Rbar_minus_0_l: forall (a:Rbar),
Rbar_minus a (Finite 0) = a.
intro.
unfold Rbar_minus.
rewrite Rbar_opp_0.
apply Rbar_plus_0_r.
Qed.

Lemma Rbar_minus_pos_eq :forall(x:Rbar)(y:Rbar)(z:Rbar),
x = y -> Rbar_minus x z = Rbar_minus y z.
intros.
rewrite H.
reflexivity.
Qed.

Lemma Rbar_minus_exchange: forall(a:R)(b:Rbar),
Rbar_minus (Rbar_opp a) b = Rbar_minus (Rbar_opp b) a.
intros.
unfold Rbar_minus.
apply Rbar_plus_comm.
Qed.



(*定义公理说明指数函数，sin，cos求导之后的结果*)
Lemma Derive_exp : forall (x:R), Derive exp x = exp x.
intro.
apply is_derive_unique.
rewrite is_derive_Reals.
apply derivable_pt_lim_exp.
Qed.

Lemma Derive_sin : forall (x:R), Derive sin x = cos x.
intro.
apply is_derive_unique.
rewrite is_derive_Reals.
apply derivable_pt_lim_sin.
Qed.

Lemma Derive_cos : forall (x:R), Derive cos x = - sin x.
intro.
apply is_derive_unique.
rewrite is_derive_Reals.
apply derivable_pt_lim_cos.
Qed.

Lemma Derive_exp_ct: forall(c x :R),
Derive (fun t => exp (c * t)) x = (fun t => (c * exp (c * t))%R) x.
intros.
rewrite comp_exp_ct_funeq.
unfold comp.
rewrite Derive_comp.
* rewrite Derive_exp.
  unfold mult_real_fct.
  rewrite Derive_scal.
  rewrite Derive_id.
  field.
* auto_derive. trivial.
* unfold mult_real_fct. auto_derive. trivial.
Qed.


(*为了之后的证明，将上述公理，换一个形式,不包含参数的形式*)
Lemma Derive_exp1: forall(c:R),
Derive (fun t => exp (c * t)) = (fun t => (c * exp (c * t))%R).
intros.
apply fun_eq.
intros.
apply Derive_exp_ct.
Qed.

Lemma Derive_cos_ct: forall(c x :R),
   Derive (fun t => cos (c * t)) x = (fun t => (-c * sin (c * t))%R) x.
intros.
rewrite comp_f_ct_funeq.
unfold comp.
rewrite Derive_comp.
* rewrite Derive_cos.
  unfold mult_real_fct.
  rewrite Derive_scal.
  rewrite Derive_id.
  field.
* auto_derive. trivial.
* unfold mult_real_fct. auto_derive. trivial.
Qed.

Lemma Derive_cos1: forall(c:R),
Derive (fun t => cos (c * t))  = (fun t => (-c * sin (c * t))%R).
intros.
apply fun_eq.
intro.
apply Derive_cos_ct.
Qed.

Lemma Derive_sin_ct : forall(c x:R),
  Derive (fun t => sin (c * t)) x = (fun t => (c * cos (c * t))%R) x.
intros.
rewrite comp_f_ct_funeq.
unfold comp.
rewrite Derive_comp.
* rewrite Derive_sin.
  unfold mult_real_fct.
  rewrite Derive_scal.
  rewrite Derive_id.
  field.
* auto_derive. trivial.
* unfold mult_real_fct. auto_derive. trivial.
Qed.

Lemma Derive_sin1: forall(c:R),
Derive (fun t => sin (c * t))  = (fun t => (c * cos (c * t))%R).
intros.
apply fun_eq.
apply Derive_sin_ct.
Qed.

(*为了之后的证明，将Coquelicot中的引理Derive引理变形为不包含参数的形式*)
Lemma Derive_opp1: forall(f:R->R),
Derive (fun x:R => (- f x)%R) = opp_fct (Derive f).
intro.
apply fun_eq.
intros.
apply Derive_opp.
Qed.


Lemma fplus_mul_ok : forall (f u v : R->R) (t : R),
  (f *f (u +f v)) t = f t * u t + f t * v t.
intros.
rewrite fmul_ok.
rewrite fplus_ok.
ring.
Qed.
(*
Lemma l1: forall(c w :R),
((fun t0 : R => - c * exp (- c * t0)) *f (fun x : R => cos (w * x)))=
(fun t:R => (- c * exp (- c * t) * cos (w * t))%R).
intros.
apply fun_eq.
intro.
rewrite fmul_ok.
ring.
Qed.

Lemma l2: forall(c w:R),
(fun x : R => exp (- c * x)) *f (fun t0 : R => - w * sin (w * t0))=
(fun t :R => (- w * exp (- c * t) * (sin ( w * t)))%R).
intros.
apply fun_eq.
intro.
rewrite fmul_ok.
ring.
Qed.


Lemma l4: forall(f:R->R)(c w:R),
RInt (fun t : R => f t * ((fun t0 : R => - c * exp (- c * t0)) *f (fun x : R => cos (w * x)) +f 
(fun x : R => exp (- c * x)) *f (fun t0 : R => - w * sin (w * t0))) t) 0 =
RInt ((f *f (fun t => (- c * exp (- c * t))%R) *f (fun t => (cos (w * t))%R)) +f 
(f *f (fun t => (exp (- c * t))%R) *f (fun t => (- w * sin (w * t))%R) )) 0.
intros.
apply fun_eq.
intro.
apply RInt_ext.
intros.
rewrite fplus_ok.
rewrite fmul_ok.
rewrite fmul_ok.
rewrite fplus_ok.
rewrite fmul_ok.
rewrite fmul_ok.
rewrite fmul_ok.
rewrite fmul_ok.
ring.
Qed.
*)

(*
Lemma l4_1: forall(f:R->R)(c:R)(w:R), 
(fun t0 : R => - c * f t0 * exp (- c * t0) * cos (w * t0))=
(fun t0 : R => - c * (f t0 * exp (- c * t0) * cos (w * t0))).
intros.
apply fun_eq.
intro.
ring.
Qed.

Lemma l4_2: forall(f:R->R)(c:R)(w:R), 
(fun t0 : R => - w * f t0 * exp (- c * t0) * sin (w * t0))=
(fun t0 : R => - w * (f t0 * exp (- c * t0) * sin (w * t0))).
intros.
apply fun_eq.
intro.
ring.
Qed.

Lemma l4: forall(f:R->R)(c:R)(w:R),
continuity f ->
(RInt (fun t => ((f t) * (Derive (fun t => ((exp (- c * t)) *(cos (w * t)) )%R )) t)%R) 0)=
(fun b => (RInt (fun t => ((- c) * (f t) * (exp (- c * t)) * (cos (w * t)))%R) 0 b)%R) +f 
(fun b => (RInt (fun t => ((- w) * (f t) * (exp (- c * t)) * (sin (w * t)))%R) 0 b)%R).
intros.
apply fun_eq.
intros.
rewrite fplus_ok.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite Derive_mult.
rewrite Derive_exp.
rewrite Derive_cos.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intros.
rewrite l4_1.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
rewrite l4_2.
intro.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_sin.
Qed.
*)

Lemma l4: forall(f:R->R)(c:R)(w:R),
continuity f ->
(RInt (fun t => ((f t) * (Derive (fun t => ((exp (- c * t)) *(cos (w * t)) )%R )) t)%R) 0)=
(fun b => (- c) * (RInt (fun t => ((f t) * (exp (- c * t)) * (cos (w * t)))%R) 0 b)%R) +f 
(fun b => (- w) * (RInt (fun t => ((f t) * (exp (- c * t)) * (sin (w * t)))%R) 0 b)%R).
intros.
apply fun_eq.
intros.
rewrite fplus_ok.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite Derive_mult.
rewrite Derive_exp_ct.
rewrite Derive_cos_ct.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intros.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_sin.
Qed.

Lemma ex_finite_lim_plus: forall(f:R->R)(g:R->R)(x:Rbar),
 ex_finite_lim f x -> ex_finite_lim g x ->
 ex_finite_lim (f +f g) x.
intros.
unfold ex_finite_lim.
unfold ex_finite_lim in H.
unfold ex_finite_lim in H0.
elim H.
intros.
elim H0.
intros.
exists (x0 + x1)%R.
apply (is_lim_plus f g x x0 x1 (x0 + x1) ).
assumption.
assumption.
reflexivity.
Qed.

Lemma l5: forall(f:R->R)(c:R)(w:R),
(fun b : R => RInt (fun t : R => - f t * exp (- c * t) * sin (w * t)) 0 b)=
(fun b : R => - RInt (fun t : R => f t * exp (- c * t) * sin (w * t)) 0 b).
intros.
apply fun_eq.
intro.
rewrite <-  RInt_opp.
apply RInt_ext.
intros.
ring.
Qed.

Lemma l6: forall(f:R->R)(c:R)(w:R),
(fun y : R => - - RInt (fun t : R => f t * exp (- c * t) * sin (w * t)) 0 y)=
(fun y : R => RInt (fun t : R => f t * exp (- c * t) * sin (w * t)) 0 y).
intros.
apply fun_eq.
intro.
rewrite Ropp_involutive.
tauto.
Qed.


(*拉普拉斯变换的微分性质*)
(* differentiation property of lapalce transform *)
Lemma lap_diff : forall (f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
derivable f ->
lap_left (Derive f) s ->
lap_right (Derive f) s ->
ex_finite_lim (f_lim_0_cos f s) p_infty -> is_lim (f_lim_0_cos f s) p_infty 0 ->
ex_finite_lim (f_lim_0_sin f s) p_infty -> is_lim (f_lim_0_sin f s) p_infty 0 ->
laplace (Derive f) s = S_CRbar_minus (S_CRbar_mul s (laplace f s)) ((f 0)%R,0%R).
unfold f_lim_0_cos.
intros.
unfold laplace.
unfold S_CRbar_minus.
unfold S_CRbar_mul.
destruct s as (c,w).
f_equal.
unfold re_lap. 
unfold re_int. 
unfold im_lap.
unfold im_int.
rewrite <- ? Lim_scal_l.
rewrite <- Lim_minus.
unfold ref.
rewrite RInt_by_parts_e1.
(*开始修改*)
rewrite RInt_by_parts.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite cos_0.
rewrite exp_0.
rewrite ? Rmult_1_r.
rewrite Lim_minus.
apply is_lim_unique in H5.
rewrite H5.
rewrite Rbar_minus_0_r.
rewrite Lim_const.
rewrite Rbar_minus_exchange.
apply Rbar_minus_pos_eq.
rewrite <- Lim_opp.
apply Lim_ext.
intro.
rewrite <- ? RInt_scal.
rewrite <- RInt_minus.
rewrite <- RInt_opp.
apply RInt_ext.
intros.
unfold imf.
rewrite Derive_mult.
rewrite Derive_exp_ct.
rewrite Derive_cos_ct.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
elim H.
intros.
apply H8.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold imf.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_pt_opp.
elim H.
intros.
apply H8.
apply continuity_exp.
apply continuity_sin.
apply ex_finite_ex_lim.
apply H4.
apply ex_lim_const.
apply ex_finite_minus.
apply H4.
unfold ex_finite_lim.
exists (f 0)%R.
apply is_lim_const.
apply H1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_cos.
elim H2.
intros.
apply H8.
rewrite Derive_mult1.
rewrite Derive_exp1.
rewrite Derive_cos1.
apply continuity_plus.
apply continuity_mult.
apply continuity_scal.
apply continuity_exp.
apply continuity_cos.
apply continuity_mult.
apply continuity_exp.
apply continuity_scal.
apply continuity_sin.
apply ex_derive_exp.
apply ex_derive_cos.
elim H2.
intros.
rewrite l3_1.
apply ex_finite_lim_correct.
split.
apply ex_lim_minus.
apply ex_finite_ex_lim.
apply H4.
apply ex_lim_const.
apply ex_finite_minus.
apply H4.
unfold ex_finite_lim.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite exp_0.
rewrite cos_0.
rewrite ? Rmult_1_r.
exists (f 0).
apply is_lim_const. 
(*apply ex_finite_lim_correct.
split.
apply ex_lim_const.
rewrite Lim_const.
apply is_finite_correct.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite exp_0.
rewrite cos_0.
rewrite ? Rmult_1_r.
exists (f 0).
tauto.*)
rewrite Lim_minus.
apply is_lim_unique in H5.
rewrite H5.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite exp_0.
rewrite cos_0.
rewrite ? Rmult_1_r.
rewrite Lim_const.
apply is_finite_correct.
rewrite Rbar_minus_0_r.
unfold Rbar_opp.
exists (- f 0).
tauto.
apply ex_finite_ex_lim.
apply H4.
apply ex_lim_const.
apply ex_finite_minus.
apply H4.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite exp_0.
rewrite cos_0.
rewrite ? Rmult_1_r.
unfold ex_finite_lim.
exists ( f 0).
apply is_lim_const.
repeat apply derivable_mult.
apply H1.
apply ex_derive_exp.
apply ex_derive_cos. 
rewrite Derive_mult1.
apply continuity_plus.
apply continuity_mult.
elim H2.
intros.
apply H8.
apply continuity_mult.
apply continuity_exp.
apply continuity_cos.
apply continuity_mult.
elim H0.
intros.
apply H10.
rewrite Derive_mult1.
apply continuity_plus.
apply continuity_mult.
rewrite Derive_exp1.
apply continuity_scal.
apply continuity_exp.
apply continuity_cos.
apply continuity_mult.
apply continuity_exp.
rewrite Derive_cos1.
apply continuity_scal.
apply continuity_sin.
apply ex_derive_exp.
apply ex_derive_cos.
apply H1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_cos.
(*第二天修改*)
rewrite l4.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
elim H.
intros.
apply H9.
apply ex_finite_lim_scal_l.
elim H0.
intros.
rewrite l5 in H9.
apply ex_finite_lim_opp in H9.
rewrite l6 in H9.
apply H9.
apply derivable_continuous.
apply H1.
unfold ref.
apply ex_lim_scal_l.
apply ex_finite_ex_lim.
elim H.
intros.
apply H9.
apply ex_lim_scal_l.
unfold imf.
apply ex_finite_ex_lim.
elim H0.
intros.
apply H9.
apply ex_finite_minus.
unfold ref.
apply ex_finite_lim_scal_l.
elim H.
intros.
apply H9.
unfold imf.
apply ex_finite_lim_scal_l.
elim H0.
intros.
apply H9.
(*整个实部证明完成,虚部可以通过类似的方法完成证明*)










































































































































































