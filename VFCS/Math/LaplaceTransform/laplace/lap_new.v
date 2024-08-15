Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
Require Import Coquelicot.AutoDerive. (* auto_derive *)
Require Import Psatz.
Open Scope R_scope.

Require Import functional.
Require Import complex2.

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
Definition re_lap f (s:C) : R := Lim (re_int f s) p_infty.
Definition im_lap f (s:C) : R := Lim (im_int f s) p_infty.

Definition laplace (f:R->R)(s:C) :C :=
 (re_lap f s, im_lap f s ).


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

(* 下面四个引理是为了laplace性质在实际应用中更好用 *)
Lemma finite_plus: forall(a b:Rbar),
is_finite a -> is_finite b ->
Rbar_plus a b = a + b.
intros.
apply is_finite_correct in H.
elim H.
apply is_finite_correct in H0.
elim H0.
intros.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma finite_minus: forall(a b:Rbar),
is_finite a -> is_finite b ->
Rbar_minus a b = a - b.
intros.
apply is_finite_correct in H.
elim H.
apply is_finite_correct in H0.
elim H0.
intros.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma finite_mult: forall(a b:Rbar),
is_finite a -> is_finite b ->
Rbar_mult a b = a * b.
intros.
apply is_finite_correct in H.
elim H.
apply is_finite_correct in H0.
elim H0.
intros.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma finite_opp: forall(a:Rbar),
is_finite a ->
Rbar_opp a = - a.
intros.
apply is_finite_correct in H.
elim H.
intros.
rewrite H0.
reflexivity.
Qed.


(* 下面四个引理将极限运算表示成 R 上的运算 *)
Lemma Lim_finite_plus (f g : R -> R) (x : Rbar) :
  ex_finite_lim f x -> ex_finite_lim g x ->
  Lim (fun y => f y + g y) x =  (Lim f x) + (Lim g x).
intros.
rewrite Lim_plus.
apply finite_plus.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_plus.
assumption.
assumption.
Qed.

Lemma Lim_finite_minus (f g : R -> R) (x : Rbar) :
  ex_finite_lim f x -> ex_finite_lim g x ->
  Lim (fun y => f y - g y) x =  (Lim f x) - (Lim g x).
intros.
rewrite Lim_minus.
apply finite_minus.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_lim_correct.
assumption.
apply ex_finite_minus.
assumption.
assumption.
Qed.

Lemma Lim_finite_scal_l: forall(f : R -> R) (a : R) (x : Rbar),
  ex_finite_lim f x ->
  Lim (fun y => a * f y) x =  a * Lim f x. 
intros.
rewrite Lim_scal_l.
apply finite_mult.
reflexivity.
apply ex_finite_lim_correct.
assumption.
Qed.

Lemma Lim_finite_opp (f : R -> R) (x : Rbar) :
ex_finite_lim f x ->
Lim (fun y => - f y) x = - (Lim f x).
rewrite Lim_opp.
intro.
apply finite_opp.
apply ex_finite_lim_correct.
assumption.
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
extensionality t.
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

(*2018/6/6对存在性前提做了改进*)
Definition lap_exit (f:R->R)(s:C): Prop := let (c,w) := s in
continuity f /\ ex_finite_lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty /\
ex_finite_lim (fun b => RInt (fun t => ((- f t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty.

Lemma lap_c_exit:forall(f:R->R)(s:C)(m:R),
lap_exit f s -> lap_exit (m *c f) s.
intros.
unfold lap_exit.
destruct s as (c,w).
split.
apply continuity_scal.
apply H.
split.
rewrite lap_c_left_pre.
apply ex_finite_lim_scal_l.
apply H.
rewrite lap_c_right_pre.
apply ex_finite_lim_scal_l.
apply H.
Qed.

(*2018/6/6对存在性前提做了改进*)
(* Laplace (c * f) = c * Laplace(f) *)
Lemma const_lap : forall(f:R->R)(s:C)(m:R),
lap_exit f s ->
laplace (m *c f) s = Cmult m (laplace f s).
destruct s as (c,w).
intros.
simpl.
unfold laplace.
f_equal.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
unfold re_lap.
(*
Current Subgoal: 
 Lim (re_int (m *c f) s) p_infty = m * Lim (re_int f s) p_infty

Rewriting lemma:
Lemma Lim_finite_scal_l: forall(f : R -> R) (a : R) (x : Rbar),
  ex_finite_lim f x ->
  Lim (fun y => a * f y) x =  a * Lim f x.
  Lim (fun y => a * f y) x =  a * Lim f x.

Error: Found no subterm matching "Finite (?M2473 * Lim ?M2472 ?M2474)" in the current goal.

Reason: This is because that a* Lim f x is automatically coerced to Finite(a* Lim f x) since the 
output of Lim is of type RBar.
*)
(* chen *)
assert( m * Lim (re_int f (c,w)) p_infty =
Finite( m * Lim (re_int f (c,w)) p_infty)).
reflexivity.
rewrite H0.
(* chen *)
f_equal.
rewrite <- Lim_finite_scal_l.
apply Lim_ext.
intro.
unfold re_int.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold ref.
rewrite fconst_ok.
ring.
apply H.
rewrite Rmult_0_l.
rewrite Rplus_0_l.
unfold im_lap.
assert ( m * real (Lim (im_int f (c, w)) p_infty) =
Finite ( m * real (Lim (im_int f (c, w)) p_infty))).
reflexivity.
rewrite H0.
f_equal.
rewrite <- Lim_finite_scal_l.
apply Lim_ext.
intro.
unfold im_int.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold imf.
rewrite fconst_ok.
ring.
apply H.
Qed.

(*
Definition C2CRbar (c:C) : CRbar := 
  let (a,b) := c in
    (Finite a,Finite b).

Coercion C2CRbar : C >-> CRbar.
*)

(*2018/6/6对存在性前提做了改进*)
(*Laplace (f + g) = (Laplace f) + (Laplace g)*)
Lemma lap_plus: forall(u:R->R)(v:R->R)(s:C),
lap_exit u s ->
lap_exit v s ->
 laplace (u +f v) s= Cplus (laplace u s) (laplace v s).
destruct s as (c,w). (* C to CRbar coercion needed *)
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
assert ((Lim (re_int u (c, w)) p_infty) + (Lim (re_int v (c, w)) p_infty) =
Finite ((Lim (re_int u (c, w)) p_infty) + (Lim (re_int v (c, w)) p_infty))).
reflexivity.
rewrite H1.
f_equal.
rewrite <- Lim_finite_plus.
apply Lim_ext.
intro.
unfold re_int.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref.
rewrite fplus_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold ref.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold ref.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply H0.
apply continuity_exp.
apply continuity_cos.
apply H.
apply H0.
(*im_lap*)
unfold im_lap.
assert ((Lim (im_int u (c, w)) p_infty) + (Lim (im_int v (c, w)) p_infty)=
Finite ((Lim (im_int u (c, w)) p_infty) + (Lim (im_int v (c, w)) p_infty))).
reflexivity.
rewrite H1.
rewrite <- Lim_finite_plus.
f_equal.
apply Lim_ext.
intro.
unfold im_int.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold imf.
rewrite fplus_ok.
ring.
unfold imf.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
apply H.
apply continuity_exp.
apply continuity_sin.
unfold imf.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
apply H0.
apply continuity_exp.
apply continuity_sin.
apply H.
apply H0.
Qed.

(*2018/6/6对存在性前提做了改进*)
(* The first method to prove the line property *)
Lemma lap_line: forall(u:R->R)(v:R->R)(s:C)(m:R)(n:R),
lap_exit u s ->
lap_exit v s ->
laplace (m *c u +f n *c v) s = Cplus (Cmult m (laplace u s)) (Cmult n (laplace v s)).
intros.
rewrite <- ? const_lap.
apply lap_plus.
apply lap_c_exit.
assumption.
apply lap_c_exit.
apply H0.
assumption.
assumption.
Qed.


Definition exp_f_mul (f:R->R)(a:R)(t:R):R :=
exp (a * t) * f t.


(* 复频域位移性质 L[e^at * f(t)] = F(s-a) *)
(*2018/6/6对存在性前提进行了改进*)
Lemma frequency_shift: forall(f:R->R)(s:C)(a:R),
lap_exit (exp_f_mul f a) s ->
lap_exit f (s - a)%C ->
laplace (exp_f_mul f a) s = laplace f (s - a)%C.
destruct s as (c,w).
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
f_equal.
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
f_equal.
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
extensionality t.
apply Derive_mult.
apply ex_derive_Reals_1.
apply H.
apply ex_derive_Reals_1.
apply H0.
Qed.


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


(*简短的表达*)
Lemma RInt_Derive1_modify: forall(f:R->R)(a b : R),
(forall x, derivable_pt f x) ->
(forall x, continuity_pt (Derive f) x) ->
RInt (Derive f) a b = (f b - f a)%R.
intros.
apply RInt_Derive.
intros.
apply ex_derive_Reals_1.
apply H.
intros.
apply continuity_equiv_continuous.
apply H0.
Qed.


Definition continuous_diff2 (f:R->R)(g:R->R):=
(forall x, ex_derive f x) /\ (forall x, ex_derive g x) /\ 
(forall x, continuity_pt (Derive f) x) /\ (forall x, continuity_pt (Derive g) x).

(* 2017/7/20*)
Lemma l3_modify: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
(fun b => RInt (fun t:R => (Derive (f *f g) t)%R) 0 b)=
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
extensionality t.
rewrite RInt_Derive1_modify.
tauto.
intros.
apply derivable_pt_mult.
apply ex_derive_Reals_0.
apply H.
apply ex_derive_Reals_0.
apply H.
intro.
rewrite Derive_mult1.
apply continuity_plus.
apply continuity_mult.
unfold continuity.
apply H.
unfold continuity.
intro.
(*可导推出可微*)
apply derivable_continuous_pt.
apply ex_derive_Reals_0.
apply H.
apply continuity_mult.
apply derivable_continuous.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
unfold continuity.
intro.
apply H.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
Qed.

(*
Lemma l3_1: forall(f:R->R)(g:R->R),
derivable (f *f g) ->
continuity (Derive (f *f g))->
RInt (fun t:R => (Derive (f *f g) t)%R) 0 =
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
apply fun_eq.
intros.
rewrite RInt_Derive1_modify.
tauto.
intros.
apply H.
intros.
apply H0.
Qed.
*)


(* 下面两条引理用来简化分部积分引理 *)
(*将l3_modify换个形式*)
Lemma l3_modify_2: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
(RInt (fun t:R => (Derive (f *f g) t)%R) 0 )=
(fun b =>((f *f g) b - (f *f g) 0)%R ).
intros.
apply l3_modify.
assumption.
Qed.

(*函数f和g在x处的极限值是有限实数，那么它们的差在x处的极限也存在*)
Lemma ex_finite_lim_minus: forall(f:R->R)(g:R->R)(x:Rbar),
 ex_finite_lim f x -> ex_finite_lim g x ->
 ex_finite_lim (f -f g) x.
intros.
unfold ex_finite_lim.
unfold ex_finite_lim in H.
unfold ex_finite_lim in H0.
elim H.
intros.
elim H0.
intros.
exists (x0 - x1)%R.
apply (is_lim_minus f g x x0 x1 (x0 - x1) ).
assumption.
assumption.
reflexivity.
Qed.

Lemma simplify_RInt_by_parts: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
ex_finite_lim (f *f g) p_infty ->
ex_finite_lim (RInt (fun t:R => (Derive (f *f g) t)%R) 0) p_infty.
intros.
rewrite l3_modify_2.
apply ex_finite_lim_minus.
assumption.
unfold ex_finite_lim.
exists ((f *f g) 0).
apply is_lim_const.
assumption.
Qed.

(*没有把f(0)单独提出来*)
Lemma RInt_by_parts1: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
ex_finite_lim (RInt (fun t:R => (Derive (f *f g) t)%R) 0) p_infty ->
ex_finite_lim (RInt (fun t:R => ((f t)*(Derive g t))%R) 0) p_infty ->

Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty  =
(Lim (fun b => RInt (fun t:R => (Derive (f *f g) t)%R ) 0 b) p_infty) - 
(Lim (fun b => RInt (fun t:R => ((f t) * (Derive g t))%R ) 0 b) p_infty).

intros.
rewrite <- Lim_finite_minus.
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
apply H.
apply H.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold fmul.
rewrite Derive_mult1.
apply continuity_pt_plus.
apply continuity_pt_mult.
apply H.
apply derivable_continuous_pt.
apply ex_derive_Reals_0.
apply H.
apply continuity_pt_mult.
apply derivable_continuous_pt.
apply ex_derive_Reals_0.
apply H.
apply H.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply derivable_continuous_pt.
apply ex_derive_Reals_0.
apply H.
apply H.
assumption.
assumption.
Qed.

(*把常数f(0)单独提出来*)
Lemma L1: forall(f g: R->R),
ex_finite_lim (fun b : R => (f *f g) b) p_infty ->
Lim (fun b => ((f *f g) b - (f *f g) 0)%R) p_infty =
(Lim (fun b => (f *f g) b ) p_infty ) - ((f *f g) 0).
intros.
rewrite Lim_finite_minus.
rewrite Lim_const.
tauto.
assumption.
unfold ex_finite_lim.
exists ((f *f g) 0).
apply is_lim_const.
Qed.



(*修改后的分部积分*)
(*根据simplify_RInt_by_parts修改了*)
Lemma RInt_by_parts2: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
ex_finite_lim (f *f g) p_infty ->
ex_finite_lim (RInt (fun t:R => ((f t)*(Derive g t))%R) 0) p_infty ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty  =
(Lim (fun b => ((f *f g) b - (f *f g) 0)%R) p_infty) -
(Lim (fun b => RInt (fun t:R => ((f t) * (Derive g t))%R ) 0 b) p_infty).
intros.
rewrite <- l3_modify.
apply RInt_by_parts1.
assumption.
apply simplify_RInt_by_parts in H0.
assumption.
assumption.
assumption.
assumption.
Qed.


(* 2017/8/18 *)
Lemma RInt_by_parts: forall(f:R->R)(g:R->R),
continuous_diff2 f g ->
ex_finite_lim (f *f g) p_infty ->
ex_finite_lim (RInt (fun t:R => ((f t)*(Derive g t))%R) 0) p_infty ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty  =
(Lim (fun b => (f *f g) b ) p_infty  - ((f *f g) 0)) -
(Lim (fun b => RInt (fun t:R => ((f t) * (Derive g t))%R ) 0 b) p_infty). 
intros.
assert ((real (Lim (fun b : R => (f *f g) b) p_infty) - (f *f g) 0) =
Finite (real (Lim (fun b : R => (f *f g) b) p_infty) - (f *f g) 0)).
reflexivity.
rewrite H2.
rewrite <- L1.
apply RInt_by_parts2.
assumption.
assumption.
assumption.
assumption.
Qed.



(*分部积分的定义有两个函数f和g的乘积，后面证明中出现三个函数的乘积，需要将函数变形为右结合*)
Lemma RInt_by_parts_e1: forall(f:R->R)(c:R)(w:R),
(fun b:R => RInt (fun t:R => ((Derive f t) * (exp (- c * t)) * (cos (w * t)))%R) 0 b) = 
(fun b:R => RInt (fun t:R => ((Derive f t) * ((exp (- c * t)) * (cos (w * t))))%R) 0 b).
intros.
extensionality t.
apply RInt_ext.
intros.
ring.
Qed.

(*将函数变为右结合，便于后续的证明，用于虚部*)
Lemma RInt_by_parts_e2: forall(f:R->R)(c:R)(w:R),
(fun t:R => ((- Derive f t) * (exp (- c * t)) * (sin (w * t)))%R) = 
(fun t:R => ((Derive (fun x:R => (- f x)%R ) t) * ((exp (- c * t)) * (sin (w * t))))%R).
intros.
extensionality t.
rewrite <- Derive_opp.
ring.
Qed.


(*证明指数函数，sin，cos求导之后的结果*)
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

(*将两个函数积分的和转化为和的积分，被积函数涉及到指数函数和cos ct的求导*)
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

(*将两个函数积分的和转化为和的积分，被积函数涉及到指数函数和sin ct的求导*)
Lemma l4_1: forall(f:R->R)(c:R)(w:R),
continuity f ->
(RInt (fun t => ((- f t) * (Derive (fun t => ((exp (- c * t)) *(sin (w * t)) )%R )) t)%R) 0)=
(fun b => c * (RInt (fun t => ((f t) * (exp (- c * t)) * (sin (w * t)))%R) 0 b)%R) +f 
(fun b => (- w) * (RInt (fun t => ((f t) * (exp (- c * t)) * (cos (w * t)))%R) 0 b)%R).
intros.
apply fun_eq.
intro.
rewrite fplus_ok.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite Derive_mult.
rewrite Derive_exp_ct.
rewrite Derive_sin_ct.
ring.
auto_derive. trivial.
auto_derive. trivial.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
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

(*l5-l8都是简单的变换等式形式*)
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

Lemma l7: forall (f:R->R)(c:R)(w:R),
(fun t:R => (f t * exp (- c * t) * cos (w * t))%R)=
(f *f (fun t:R => (exp (- c * t) * cos (w * t))%R)).
intros.
extensionality t.
rewrite fmul_ok.
field.
Qed.

Lemma l8: forall (f:R->R)(c:R)(w:R),
(fun t:R => (- f t * exp (- c * t) * sin (w * t))%R)=
((fun t => (- f t)%R) *f (fun t:R => (exp (- c * t) * sin (w * t))%R)).
intros.
extensionality t.
rewrite fmul_ok.
field.
Qed.

Lemma Rplus_opp: forall(a b:R),
a + -b = a - b.
intros.
trivial.
Qed. 

Lemma Rminus_exchange: forall(a b c:R),
a-b-c = a-c-b.
intros.
ring.
Qed.

Lemma Rminus_eq_reg_r: forall(r r1 r2:R),
r1 = r2 -> r1 -r = r2 -r.
intros.
rewrite H.
trivial.
Qed.

(*2018/10/9边看边修改*)
(*2018/6/6将laplace变换存在性改进后的证明*)
(*2017/8/21继续修改*)
(*2017/8/18再次修改，使用复数C上的运算*)
(*2017/8/14修改 使用上述的引理RInt_by_parts*)
Lemma lap_diff1 : forall (f:R->R)(s:C),
lap_exit f s ->
derivable f ->
lap_exit (Derive f) s ->
ex_finite_lim (ref f s) p_infty -> is_lim (ref f s) p_infty 0 ->
ex_finite_lim (imf f s) p_infty -> is_lim (imf f s) p_infty 0 ->
laplace (Derive f) s = Cminus ( Cmult s (laplace f s)) (f 0).
destruct s as (c,w).
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap. 
unfold im_lap.
assert (c * (Lim (re_int f (c, w)) p_infty) =
Finite (c * (Lim (re_int f (c, w)) p_infty))).
reflexivity.
rewrite H6.
rewrite <- Lim_finite_scal_l.
assert ( w * (Lim (im_int f (c, w)) p_infty)=
Finite (w * (Lim (im_int f (c, w)) p_infty))).
reflexivity.
rewrite H7.
rewrite <- Lim_finite_scal_l.
assert ((Lim (fun y : R => c * re_int f (c, w) y) p_infty)
- (Lim (fun y : R => w * im_int f (c, w) y) p_infty) =
Finite ((Lim (fun y : R => c * re_int f (c, w) y) p_infty) 
- (Lim (fun y : R => w * im_int f (c, w) y) p_infty))).
reflexivity.
rewrite H8.
rewrite <- Lim_finite_minus.
rewrite Rplus_opp.
unfold re_int.
unfold ref.
rewrite RInt_by_parts_e1.
(*开始修改*)
rewrite RInt_by_parts.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite cos_0.
rewrite exp_0.
rewrite ? Rmult_1_r.
rewrite Rminus_exchange.
(*去掉最外层的real Finite*)
simpl.
apply Rminus_eq_reg_r. 
rewrite <- l7.
(*2018/6/6*)
apply is_lim_unique in H3.
unfold ref in H3.
rewrite H3.
rewrite Rminus_0_l.
(* Lemma Lim_finite_opp (f : R -> R) (x : Rbar) :
ex_finite_lim f x ->
Lim (fun y => - f y) x = - (Lim f x). *)
assert (- (Lim (fun b : R => RInt (fun t : R => f t * Derive (fun t0 : R => exp (- c * t0) * cos (w * t0)) t) 0 b) p_infty)=
Finite (- (Lim (fun b : R => RInt (fun t : R => f t * Derive (fun t0 : R => exp (- c * t0) * cos (w * t0)) t) 0 b) p_infty))).
reflexivity.
rewrite H9.
rewrite <- Lim_finite_opp.
f_equal.
apply Lim_ext.
intro.
unfold im_int.
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
(* 上面代码杀死脑细胞无数 各种隐式类型转化 头都疼了*)
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold imf.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_pt_opp.
apply H.
apply continuity_exp.
apply continuity_sin.
unfold ref in H2.
(* 下面也开始作怪咯 *)
rewrite l4.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
unfold lap_exit in H.
elim H.
intros.
elim H11.
intros.
rewrite l5 in H13.
apply ex_finite_lim_opp in H13.
rewrite l6 in H13.
apply H13.
apply derivable_continuous.
assumption.
unfold continuous_diff2.
split.
intros. 
apply ex_derive_Reals_1.
apply H0.
split.
intro.
apply ex_derive_Reals_1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_cos.
split.
apply H1.
intro.
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
rewrite <- l7.
apply H2.
rewrite l4.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
elim H.
intros.
elim H10. intros.
rewrite l5 in H12.
apply ex_finite_lim_opp in H12.
rewrite l6 in H12.
apply H12.
apply derivable_continuous.
apply H0.
unfold re_int.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
unfold im_int.
unfold imf.
apply H.
apply H.
apply H.
(*2018/6/6将存在性性质进行改进后，实部的证明结束*)
(*整个实部证明完成,虚部可以通过类似的方法完成证明*)
unfold re_lap.
unfold im_lap.
assert (w * (Lim (re_int f (c, w)) p_infty) =
Finite (w * (Lim (re_int f (c, w)) p_infty))).
reflexivity.
rewrite H6.
rewrite <- Lim_finite_scal_l.
assert ( c * (Lim (im_int f (c, w)) p_infty)=
Finite ( c * (Lim (im_int f (c, w)) p_infty))).
reflexivity.
rewrite H7.
rewrite <- Lim_finite_scal_l.
assert ((Lim (fun y : R => w * re_int f (c, w) y) p_infty)
+ (Lim (fun y : R => c * im_int f (c, w) y) p_infty) =
Finite ((Lim (fun y : R => w * re_int f (c, w) y) p_infty) 
+ (Lim (fun y : R => c * im_int f (c, w) y) p_infty))).
reflexivity.
rewrite H8.
rewrite <- Lim_finite_plus.
rewrite Ropp_0.
rewrite Rplus_0_r.
f_equal.
unfold im_int.
unfold imf.
rewrite RInt_by_parts_e2.
(*开始修改*)
rewrite RInt_by_parts.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
(* 修改到这啦*)
rewrite sin_0.
rewrite exp_0.
rewrite ? Rmult_0_r.
rewrite Rminus_0_r.
rewrite <- l8.
apply is_lim_unique in H5.
unfold imf in H5.
rewrite H5.
rewrite Rminus_0_l.
rewrite <- Lim_finite_opp.
apply Lim_ext.
intro.
unfold re_int.
rewrite <- ? RInt_scal.
rewrite <- RInt_opp.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref. 
rewrite Derive_mult.
rewrite Derive_exp_ct.
rewrite Derive_sin_ct.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply H.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_pt_opp.
apply H.
apply continuity_exp.
apply continuity_sin.
unfold ref in H4.
rewrite l4_1.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
(*
unfold lap_exit in H.
elim H.
intros.
elim H11.
intros.
rewrite l5 in H13.
apply ex_finite_lim_opp in H13.
rewrite l6 in H13.
apply H13.
*)
unfold lap_exit in H.
elim H.
intros.
elim H10.
intros.
rewrite l5 in H12.
apply ex_finite_lim_opp in H12.
rewrite l6 in H12.
assumption.
apply ex_finite_lim_scal_l.
apply H.
apply H.
unfold continuous_diff2.
split.
intros.
apply ex_derive_Reals_1.
apply derivable_pt_opp.
apply H0.
split.
intro.
apply ex_derive_Reals_1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_sin.
split.
intro.
rewrite Derive_opp1.
apply continuity_pt_opp.
apply H1.
intro.
rewrite Derive_mult1.
rewrite Derive_exp1.
rewrite Derive_sin1.
apply continuity_plus.
apply continuity_mult.
apply continuity_scal.
apply continuity_exp.
apply continuity_sin.
apply continuity_mult.
apply continuity_exp.
apply continuity_scal.
apply continuity_cos.
apply ex_derive_exp.
apply ex_derive_sin.
rewrite <- l8.
assumption.
rewrite l4_1.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
elim H.
intros.
elim H10.
intros.
rewrite l5 in H12.
apply ex_finite_lim_opp in H12.
rewrite l6 in H12.
apply H12.
apply ex_finite_lim_scal_l.
apply H.
apply H.
unfold re_int.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
apply H.
apply H.
apply H.
Qed.
(*虚部证明完成*)

(*2018/3/15*)
(*2018/10/9针对*)
(*f=g -> L[f]=L[g]*)
Lemma lap_ext:forall(f g:R->R)(s:C),
lap_exit f s -> lap_exit g s ->f = g ->
laplace f s = laplace g s.
intros.
rewrite H1.
reflexivity.
Qed.

Lemma RInt_0_0:forall(f:R->R),
RInt f 0 0 = 0.
intros.
apply RInt_point.
Qed.

Require Import Coquelicot.RInt_analysis.

Lemma ex_derive_RInt: forall(f:R->R)(x:R), 
continuity f -> ex_derive (RInt f 0) x.
intros. auto_derive. split. apply ex_RInt_Reals_1. apply continuity_implies_RiemannInt1.
intros.
apply H.
split.
(*
Lemma continuity_pt_locally :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps).
*)

(*
Lemma continuity_pt_ext_loc :
  forall f g x,
  locally x (fun x => f x = g x) ->
  continuity_pt f x -> continuity_pt g x.
*)

Admitted.

(*
Lemma Derive_RInt (f : R -> R) (a b : R) :
  locally b (ex_RInt f a) -> continuous f b
  -> Derive (RInt f a) b = f b.
*)
(*这条引理类似于RInt_analysis库中的引理Derive_RInt*)
Lemma Derive_RInt1:forall(f:R->R),
(forall t:R,locally t (ex_RInt f 0))->
continuity f -> Derive (RInt f 0) = f.
intros.
extensionality t.
apply Derive_RInt.
apply H.
apply continuity_equiv_continuous.
apply H0.
Qed.

Lemma Derive_RInt2:forall(f:R->R)(b:R),
locally b (ex_RInt f 0) -> continuity f->
Derive (RInt f 0) b= f b.
intros.
apply Derive_RInt.
assumption.
apply continuity_equiv_continuous.
apply H0.
Qed.

(*complex2库扩充引理*)
Lemma Cminus_0_r:forall(r:C),
Cminus r 0 = r.
carith1 r.
Qed.

(*积分性质*)
Lemma lap_int1: forall(f:R->R)(s:C),
(forall t:R,locally t (ex_RInt f 0))->
derivable (RInt f 0) ->
lap_exit f s ->
lap_exit (RInt f 0) s ->
ex_finite_lim (ref (RInt f 0) s) p_infty ->
is_lim (ref (RInt f 0) s) p_infty 0 ->
ex_finite_lim (imf (RInt f 0) s) p_infty ->
is_lim (imf (RInt f 0) s) p_infty 0 ->
laplace f s = Cmult s (laplace (RInt f 0) s).
destruct s as (c,w).
(*laplace (Derive f) s = Cminus ( Cmult s (laplace f s)) (f 0).*)
intros.
rewrite <- Cminus_0_r.
rewrite <- (RInt_0_0 f) at 2.
rewrite <- lap_diff1.
apply lap_ext.
assumption.
rewrite Derive_RInt1.
assumption.
assumption.
apply H1.
apply sym_eq.
apply Derive_RInt1.
assumption.
apply H1.
assumption.
assumption.
rewrite Derive_RInt1.
assumption.
assumption.
apply H1.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma Rmult_eq_reg_l: forall(r r1 r2:C),
r1 = r2 -> Cmult r r1 = Cmult r r2.
intros.
rewrite H.
trivial.
Qed.

(*2018/10/9*)
Lemma Cinv_r : forall r:C, r <> 0 -> Cmult r (Cinv r) = 1.
destruct r as (a,b).
intro.
compute.
f_equal.
field. 
apply square_plus_not_zero.
assumption.
field; apply square_plus_not_zero;
assumption.
Qed.

(*laplace f s = Cmult s (laplace (RInt f 0) s).*)
Lemma lap_int_pre1:forall(f:R->R)(s:C),
(forall t:R,locally t (ex_RInt f 0))->
derivable (RInt f 0) ->
lap_exit (Derive (RInt f 0)) s->
lap_exit f s ->
lap_exit (RInt f 0) s ->
ex_finite_lim (ref (RInt f 0) s) p_infty ->
is_lim (ref (RInt f 0) s) p_infty 0 ->
ex_finite_lim (imf (RInt f 0) s) p_infty ->
is_lim (imf (RInt f 0) s) p_infty 0 ->
Cmult (Cinv s) (laplace f s) = Cmult (Cinv s) (Cmult s (laplace (RInt f 0) s)).
intros.
apply Rmult_eq_reg_l.
apply lap_int1.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
Qed.


Lemma lap_int_pre2:forall(f:R->R)(s:C),
s<> 0 ->
Cmult (Cinv s) (Cmult s (laplace (RInt f 0) s)) = laplace (RInt f 0) s.
intros.
rewrite <- Cmult_assoc.
replace (Cmult (Cinv s) s) with (IRC 1).
apply Cmult_1_r.
apply sym_eq.
(*Lemma Cinv_l : forall r:C, r <> 0 -> / r * r = 1.*)
apply Cinv_l.
assumption.
Qed.

(*2018/10/9*)
Lemma lap_int: forall(f:R->R)(s:C),
s<>0 ->
(forall t:R,locally t (ex_RInt f 0))->
derivable (RInt f 0) ->
lap_exit (Derive (RInt f 0)) s->
lap_exit f s ->
lap_exit (RInt f 0) s ->
ex_finite_lim (ref (RInt f 0) s) p_infty ->
is_lim (ref (RInt f 0) s) p_infty 0 ->
ex_finite_lim (imf (RInt f 0) s) p_infty ->
is_lim (imf (RInt f 0) s) p_infty 0 ->
 (laplace (RInt f 0) s) =  Cmult (Cinv s) (laplace f s).
intros.
apply sym_eq.
rewrite lap_int_pre1.
rewrite lap_int_pre2.
tauto.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
Qed.

(*2018/10/9定义二阶导数*)
Definition Derive2 (f:R->R)(t:R):R :=
Derive (Derive f) t.

Definition derivable2 (f:R->R):=
(forall x, ex_derive f x) /\ (forall x, ex_derive (Derive f) x).

(*
laplace (Derive f) s = Cminus ( Cmult s (laplace f s)) (f 0).
*)
Lemma diff2:forall(f:R->R)(s:C),
derivable2 f ->
lap_exit f s ->
lap_exit (Derive f) s ->
lap_exit (Derive2 f) s ->
ex_finite_lim (ref f s) p_infty -> is_lim (ref f s) p_infty 0 ->
ex_finite_lim (imf f s) p_infty -> is_lim (imf f s) p_infty 0 ->
ex_finite_lim (ref (Derive f) s) p_infty -> is_lim (ref (Derive f) s) p_infty 0 ->
ex_finite_lim (imf (Derive f) s) p_infty -> is_lim (imf (Derive f) s) p_infty 0 ->
laplace (Derive2 f) s = Cminus (Cmult s (Cminus ( Cmult s (laplace f s)) (f 0))) ((Derive f) 0).
intros.
unfold Derive2.
rewrite lap_diff1.
rewrite lap_diff1.
tauto.
assumption.
unfold derivable.
intros.
apply ex_derive_Reals_0.
apply H.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
unfold derivable.
intros.
apply ex_derive_Reals_0.
apply H.
apply H2.
assumption.
assumption.
assumption.
assumption.
Qed.


(*复数库扩充引理*)
Lemma Cmult_minus_distr_l:forall(r1 r2 r3:C),
(r1 * (r2 - r3))%C = (r1 * r2 - r1 * r3)%C.
intros.
carith3 r1 r2 r3.
Qed.

Lemma diff2_1:forall(f:R->R)(s:C),
Cminus (Cmult s (Cminus ( Cmult s (laplace f s)) (f 0))) ((Derive f) 0)=
Cminus (Cminus (Cmult (Cmult s s) (laplace f s)) (Cmult s (f 0))) ((Derive f) 0).
intros.
rewrite Cmult_minus_distr_l.
rewrite <- Cmult_assoc.
tauto.
Qed.

Lemma diff2_2:forall(f:R->R)(s:C),
derivable2 f ->
lap_exit f s ->
lap_exit (Derive f) s ->
lap_exit (Derive2 f) s ->
ex_finite_lim (ref f s) p_infty -> is_lim (ref f s) p_infty 0 ->
ex_finite_lim (imf f s) p_infty -> is_lim (imf f s) p_infty 0 ->
ex_finite_lim (ref (Derive f) s) p_infty -> is_lim (ref (Derive f) s) p_infty 0 ->
ex_finite_lim (imf (Derive f) s) p_infty -> is_lim (imf (Derive f) s) p_infty 0 ->
laplace (Derive2 f) s = Cminus (Cminus (Cmult (Cmult s s) (laplace f s)) (Cmult s (f 0))) ((Derive f) 0).
intros.
rewrite <- diff2_1.
apply diff2.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
Qed.

Definition ex_finite_lim_value_zero (f:R->R)(s:C):=
ex_finite_lim (ref f s) p_infty /\ is_lim (ref f s) p_infty 0 /\
ex_finite_lim (imf f s) p_infty /\ is_lim (imf f s) p_infty 0.

Lemma diff2_3:forall(f:R->R)(s:C),
derivable2 f ->
lap_exit f s ->
lap_exit (Derive f) s ->
lap_exit (Derive2 f) s ->
ex_finite_lim_value_zero f s ->
ex_finite_lim_value_zero (Derive f) s->
laplace (Derive2 f) s = Cminus (Cminus (Cmult (Cmult s s) (laplace f s)) (Cmult s (f 0))) ((Derive f) 0).
intros.
apply diff2_2.
apply H.
apply H0.
assumption.
assumption.
apply H3.
apply H3.
apply H3.
apply H3.
apply H4.
apply H4.
apply H4.
apply H4.
Qed.

(*
(*短周期传递函数模型的推导*)
Parameters X U: RF2.
Parameters A B: RM2.
Parameters s :C.

Axiom e1: derive_RV2 X =RF2_plus (RF2_cmul A X) (RF2_cmul B U).
(*零初始条件*)
Axiom e2: RF2_app X 0 = (0,0).

(*2018/6/7增加了零初始条件*)
Definition verify_pre X U s :Prop:=
ex_derive_RF2 X /\RF2_app X 0 = (0%R,0%R) /\
lap_left_v2 X s /\ lap_right_v2 X s /\ lap_left_v2 U s /\ lap_right_v2 U s /\
lap_left_v2 (derive_RV2 X) s /\ lap_right_v2 (derive_RV2 X) s /\ 
ex_finite_lim_re_v2 X s /\ is_lim_re_v2 X s /\
ex_finite_lim_im_v2 X s /\ is_lim_im_v2 X s.
*)

Parameters Vf If Tm Om:R->R.
Parameters rf lf km J F K:R.
Parameters s:C.

(*零初始条件*)
Axiom e1: If 0 = 0.
Axiom e2: Om 0 = 0.
Axiom e3: (Derive Om) 0 = 0.

Axiom e4: Vf = (rf *c If) +f (lf *c (Derive If)).
Axiom e5: Tm = km *c If.
Axiom e6: Tm = (J *c (Derive (Derive Om))) +f (F *c (Derive Om)) +f (K *c Om).

Definition verify_pre:Prop :=
lap_exit Vf s /\ lap_exit If s /\lap_exit Tm s /\lap_exit Om s/\ 
lap_exit (Derive If) s /\ lap_exit (Derive Om) s /\lap_exit (Derive2 Om) s /\
(forall x, ex_derive If x)/\(forall x, ex_derive Om x)/\(forall x, ex_derive (Derive Om) x)/\
ex_finite_lim_value_zero If s /\ ex_finite_lim_value_zero Om s /\ ex_finite_lim_value_zero (Derive Om) s.
(*
ex_finite_lim (fun b : R => RInt (fun t : R => (f +f g) t * exp (- c * t) * cos (w * t)) 0 b) p_infty
*)
(*
(fun b:R => RInt (fun t:R => (((m *c f) t) * (exp (- c * t)) * (cos (w * t)) )%R) 0 b) = 
(fun b:R => (m * (RInt (fun t:R => ((f t) * (exp (- c * t)) * (cos (w * t)) )%R) 0 b))%R).
*)

Lemma lap_plus_left_pre: forall(f g:R->R)(c:R)(w:R),
continuity f ->continuity g ->
(fun b : R => RInt (fun t : R => (f +f g) t * exp (- c * t) * cos (w * t)) 0 b) = 
(fun b : R => RInt (fun t : R => (f t) * exp (- c * t) * cos (w * t)) 0 b) +f 
(fun b : R => RInt (fun t : R => (g t) * exp (- c * t) * cos (w * t)) 0 b).
intros.
extensionality t.
rewrite fplus_ok.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite fplus_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
repeat apply continuity_mult.
assumption.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
repeat apply continuity_mult.
assumption.
apply continuity_exp.
apply continuity_cos.
Qed.

(*
ex_finite_lim (fun b : R => RInt (fun t : R => - (f +f g) t * exp (- c * t) * sin (w * t)) 0 b) p_infty
*)
Lemma lap_plus_right_pre: forall(f g:R->R)(c:R)(w:R),
continuity f ->continuity g ->
(fun b : R => RInt (fun t : R => - (f +f g) t * exp (- c * t) * sin (w * t)) 0 b) = 
(fun b : R => RInt (fun t : R => (- f t) * exp (- c * t) * sin (w * t)) 0 b) +f 
(fun b : R => RInt (fun t : R => (- g t) * exp (- c * t) * sin (w * t)) 0 b).
intros.
extensionality t.
rewrite fplus_ok.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite fplus_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
repeat apply continuity_mult.
apply continuity_opp.
assumption.
apply continuity_exp.
apply continuity_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
repeat apply continuity_mult.
apply continuity_opp.
assumption.
apply continuity_exp.
apply continuity_sin.
Qed.


Lemma lap_plus_exit:forall(f g:R->R)(s:C),
lap_exit f s -> lap_exit g s->
lap_exit (f +f g) s.
intros.
unfold lap_exit.
destruct s0 as (c,w).
split.
apply continuity_plus.
apply H.
apply H0.
split.
rewrite lap_plus_left_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
rewrite lap_plus_right_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
Qed.

Lemma pre1:
(lf * s * (laplace If s))%C = (lf * (s * (laplace If s)))%C.
rewrite <- Cmult_assoc.
tauto.
Qed.
(*
Lemma Cminus_0_r:forall(r:C),
Cminus r 0 = r.
*)

Lemma pre2:
(s * (laplace If s))%C = Cminus (s * (laplace If s))%C (If 0).
rewrite e1.
apply sym_eq.
apply Cminus_0_r.
Qed.

(*
laplace (Derive f) s = Cminus ( Cmult s (laplace f s)) (f 0).
*)
(*
Lemma const_lap : forall(f:R->R)(s:C)(m:R),
lap_exit f s ->
laplace (m *c f) s = Cmult m (laplace f s).
*)
Lemma robot1:
verify_pre ->
laplace Vf s = Cmult (Cplus rf (Cmult lf s)) (laplace If s).
intros.
rewrite Cmult_plus_distr_r.
rewrite <- const_lap.
rewrite pre1.
rewrite pre2.
rewrite <- lap_diff1.
rewrite <- const_lap.
rewrite <- lap_plus.
apply lap_ext.
apply H.
apply lap_plus_exit.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply e4.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply H.
apply H.
unfold derivable.
intros.
apply ex_derive_Reals_0.
apply H.
apply H.
apply H.
apply H.
apply H.
apply H.
apply H.
Qed.


Lemma robot2:
verify_pre ->
laplace Tm s = Cmult km (laplace If s).
intros.
rewrite <- const_lap.
apply lap_ext.
apply H.
apply lap_c_exit.
apply H.
apply e5.
apply H.

(*
laplace Tm s = ((J * (s * s) + F * s + K) * laplace Om s)%C
*)
Lemma pre3:forall(r1 r2 r3 r:C),
((r1 + r2 + r3) * r)%C = (r1 *r + r2 * r + r3 * r)%C.
intros.
rewrite Cmult_plus_distr_r.
rewrite Cmult_plus_distr_r.
tauto.
Qed.

Lemma Cmult_0_l : forall (r:C), (r * 0)%C = 0.
intros.
rewrite Cmult_comm.
apply Cmult_0_r.
Qed.

Lemma pre4:
Cmult (Cmult s s) (laplace Om s)=
Cminus (Cminus (Cmult (Cmult s s) (laplace Om s)) (Cmult s (Om 0))) ((Derive Om) 0).
rewrite e2.
rewrite e3.
rewrite Cminus_0_r.
rewrite Cmult_0_l.
rewrite Cminus_0_r.
tauto.
Qed.

Lemma pre5:
Cmult s (laplace Om s) = Cminus (Cmult s (laplace Om s)) (Om 0).
rewrite e2.
rewrite Cminus_0_r.
tauto.
Qed.

Lemma robot3:
verify_pre ->
laplace Tm s = Cmult (Cplus (Cplus (Cmult J (Cmult s s)) (Cmult F s)) K) (laplace Om s).
intros.
rewrite pre3.
rewrite Cmult_assoc.
rewrite pre4.
rewrite <- diff2_3.
rewrite Cmult_assoc.
rewrite pre5.
rewrite <- lap_diff1.
rewrite <- ? const_lap.
rewrite <- ? lap_plus.
apply lap_ext.
apply H.
apply lap_plus_exit.
apply lap_plus_exit.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply e6.
apply lap_plus_exit.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply lap_c_exit.
apply H.
apply H.
apply H.
apply H.
apply H.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H.
apply H.
apply H.
apply H.
apply H.
apply H.
unfold derivable2.
split.
intros.
apply H.
intros.
apply H.
apply H.
apply H.
apply H.
apply H.
apply H.
Qed.














































































































































































