Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
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

Definition RBarF := R->Rbar.
Definition CRBarF := C->Rbar.

Definition CBarF :=  (CRBarF * CRBarF)%type.
Definition CRbar := (Rbar * Rbar)%type.

(* the two parts of laplace transform of f. *)
Definition re_lap f (s:C) : Rbar := Lim (re_int f s) p_infty.
Definition im_lap f (s:C) : Rbar := Lim (im_int f s) p_infty.

(* two equivalent definitions of lapalce transform*)
Definition laplace (f : R->R): CBarF
  := (re_lap f , im_lap f).

Definition laplace2 (f:R->R)(s:C) :CRbar
  := (re_lap f s, im_lap f s ).

Definition CRBarF_plus (f1:CRBarF) (f2:CRBarF): CRBarF :=
fun t => Rbar_plus (f1 t) (f2 t).

Definition CBarF_plus (f1:CBarF) (f2:CBarF) : CBarF :=
let (f11,f12) :=  f1 in
let (f21,f22) :=  f2 in
(CRBarF_plus f11 f21, CRBarF_plus f12 f22).

Definition C_CRBarF_mul (c:R) (f:CRBarF): CRBarF :=
fun t => Rbar_mult (Finite c) (f t).

Definition C_CBarF_mul (c:R) (f:CBarF): CBarF :=
let (f1,f2) := f in
(C_CRBarF_mul c f1, C_CRBarF_mul c f2).

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


(* Laplace (c * f) = c * Laplace(f) *)
Lemma const_lap : forall (c:R)(s:C)(f:R->R),
   laplace2 (c *c f) s = C_CRbar_mul c (laplace2 f s).
intros.
simpl.
unfold laplace2.
f_equal.
unfold re_lap.
unfold re_int.
rewrite <- Lim_scal_l.
apply Lim_ext.
intro.
apply sym_eq.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold ref.
rewrite fconst_ok.
destruct s as (s1,s2).
ring.
unfold im_lap.
unfold im_int.
rewrite <- Lim_scal_l.
apply Lim_ext.
intro.
apply sym_eq.
rewrite <- RInt_scal.
apply RInt_ext.
intros.
unfold imf.
rewrite fconst_ok.
destruct s as (s1,s2).
ring.
Qed.


Axiom continuity_implies_RiemannInt1: forall (f:R->R)(a b :R),
(forall x:R, continuity_pt f x )-> Riemann_integrable f a b.

Axiom continuity_exp: forall(x:R)(c:R),continuity_pt (fun t => exp (c * t)) x.
Axiom continuity_cos: forall(x:R)(c:R),continuity_pt (fun t => cos (c * t)) x.
Axiom continuity_sin: forall(x:R)(c:R),continuity_pt (fun t => sin (c * t)) x.

(* laplace的存在性条件,用作下面引理的前提条件 *)
Definition lap_exits (f:R->R)(M:R)(c1:R)(s:C): Prop :=
let (c,w) := s in
0<M /\ 0<=c1 /\ c1<c /\ continuity f /\ (forall t, Rabs (f t) <= M * (exp (c1 * t))).

Definition lap_precondition (f:R->R)(g:R->R)(M:R)(c1:R)(s:C): Prop :=
let (c,w) := s in
0<M /\ 0<=c1 /\ c1<c /\ continuity f /\ continuity g /\ 
(forall t, Rabs(f t) <= M * (exp (c1 * t))) /\ (forall t, Rabs(g t) <= M * (exp (c1 * t))).

Definition ex_cos_precondition (f:R->R)(g:R->R)(s:C): Prop :=
let (c,w) := s in
ex_lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty /\
ex_lim (fun b => RInt (fun t => ((g t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty.

Definition ex_sin_precondition (f:R->R)(g:R->R)(s:C): Prop :=
let (c,w) := s in
ex_lim (fun b => RInt (fun t => ((- f t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty /\
ex_lim (fun b => RInt (fun t => ((- g t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty.

Definition ex_cos_plus_precondition (f:R->R)(g:R->R)(s:C): Prop :=
let (c,w) := s in
ex_Rbar_plus (Lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty)
(Lim (fun b => RInt (fun t => ((g t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty).

Definition ex_sin_plus_precondition (f:R->R)(g:R->R)(s:C): Prop :=
let (c,w) := s in
ex_Rbar_plus (Lim (fun b => RInt (fun t => ((- f t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty)
(Lim (fun b => RInt (fun t => ((- g t) * (exp (-c * t)) * (sin (w * t)))%R ) 0 b) p_infty).

Definition ex_minus_precondition (f:R->R)(g:R->R)(s:C): Prop :=
let (c,w) := s in
ex_Rbar_minus (Lim (fun b => RInt (fun t => ((f t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty)
(Lim (fun b => RInt (fun t => ((g t) * (exp (-c * t)) * (cos (w * t)))%R ) 0 b) p_infty).

(*Laplace (f + g) = (Laplace f) + (Laplace g)*)
Lemma lap_plus: forall(u:R->R) (v:R->R)(M:R)(c1:R)(s:C),
 lap_precondition u v M c1 s ->
 ex_sin_precondition u v s ->
 ex_cos_precondition u v s ->
 ex_sin_plus_precondition u v s ->
 ex_cos_plus_precondition u v s ->
 laplace2 (u +f v) s= CRbar_plus (laplace2 u s) (laplace2 v s) .
unfold lap_precondition.
unfold ex_cos_precondition.
unfold ex_sin_precondition.
unfold ex_cos_plus_precondition.
unfold ex_sin_plus_precondition.
destruct s as (c,w).
intros.
simpl.
unfold laplace2.
f_equal.
unfold re_lap.
unfold re_int.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
apply sym_eq.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref.
rewrite fplus_ok.
ring.
unfold ref.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
elim H5.
intros.
elim H7.
intros.
elim H9.
intros.
apply H10.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold ref.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
elim H5.
intros.
elim H7.
intros.
elim H9.
intros.
elim H11.
intros.
apply H12.
apply continuity_exp.
apply continuity_cos.
unfold ref.
elim H1.
intros.
apply H4.
unfold ref.
elim H1.
intros.
apply H5.
unfold ref.
apply H3.
(*im_lap*)
unfold im_lap.
unfold im_int.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
apply sym_eq.
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
elim H.
intros.
elim H5.
intros.
elim H7.
intros.
elim H9.
intros.
apply continuity_pt_opp.
apply H10.
apply continuity_exp.
apply continuity_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold imf.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
elim H5.
intros.
elim H7.
intros.
elim H9.
intros.
elim H11.
intros.
apply continuity_pt_opp.
apply H12.
apply continuity_exp.
apply continuity_sin.
unfold imf.
elim H0.
intros.
apply H4.
unfold imf.
elim H0.
intros.
apply H5.
unfold imf.
apply H2.
Qed.


(* linearity property of lapalce transform *)
(*laplace(m*f1 + n*f2)= m*laplace (f1) + n*laplace (f2)*)
Lemma lap_liner: forall (f1 f2:R->R)(m n :R),
laplace (m *c f1 +f n *c f2) =CBarF_plus (C_CBarF_mul m (laplace f1)) (C_CBarF_mul n (laplace f2)).
intros.
simpl.
unfold laplace.
f_equal.
unfold re_lap.
unfold re_int.
apply fun_eq1.
intro.
unfold CRBarF_plus.
unfold C_CRBarF_mul.
rewrite <- Lim_scal_l.
rewrite <- Lim_scal_l.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
rewrite <- RInt_scal.
apply sym_eq.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold ref.
destruct t as (t1,t2).
rewrite fplus_ok.
rewrite fconst_ok.
rewrite fconst_ok.
ring.
apply ex_RInt_Reals_1.
apply e1.
apply ex_RInt_Reals_1.
apply e1.
apply e2.
apply e2.
apply e3.
apply e2.
apply e2.
unfold im_lap.
unfold im_int.
apply fun_eq1.
intro.
unfold CRBarF_plus.
unfold C_CRBarF_mul.
rewrite <- Lim_scal_l.
rewrite <- Lim_scal_l.
rewrite <- Lim_plus.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
rewrite <- RInt_scal.
apply sym_eq.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
unfold imf.
destruct t as (t1,t2).
rewrite fplus_ok.
rewrite fconst_ok.
rewrite fconst_ok.
ring.
apply ex_RInt_Reals_1.
apply e1.
apply ex_RInt_Reals_1.
apply e1.
apply e2.
apply e2.
apply e3.
apply e2.
apply e2.
Qed.

(* integral by parts *)
Axiom RInt_by_parts : forall (f:R->R)(g:R->R)(h:R->R),
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t) * (h t))%R ) 0 b) p_infty =Rbar_minus 
(Rbar_minus (Lim (f *f g *f h) p_infty) (Lim (fun b => RInt (fun t:R => ((f t)*( Derive (fun x => g x * h x )) t)%R) 0 b) p_infty) )
(Finite ((f *f g *f h) (Finite 0))).


(* 这个引理在HOL中也是已知引理，这里先定义成公理 *)
Axiom l_exp_cos_null: forall (f:R->R)(s1:R)(s2:R),
(Lim (f *f (fun t : R => exp (- s1 * t)) *f (fun t : R => cos (s2 * t))) p_infty) = Finite 0.
Axiom l_exp_sin_null: forall (f:R->R)(s1:R)(s2:R),
Lim (f *f (fun t:R => exp (- s1 * t)) *f (fun t:R => sin (s2 * t))) p_infty = Finite 0.

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

Axiom ex_derive_exp: forall(c x:R), derivable_pt (fun t => exp (c * t)) x.
Axiom Derive_exp: forall(c x :R),
Derive (fun t => exp (c * t)) x = (fun t => (c * exp (c * t))%R) x.

Axiom ex_derive_cos: forall(c x:R), derivable_pt (fun t => cos (c * t)) x.
Axiom Derive_cos: forall(c x :R),
Derive (fun t => cos (c * t)) x = (fun t => (-c * sin (c * t))%R) x.

Axiom ex_derive_sin: forall(c x:R), derivable_pt (fun t => sin (c * t)) x.
Axiom Derive_sin: forall(c x:R),
Derive (fun t => sin (c * t)) x = (fun t => (c * cos (c * t))%R) x.

Lemma Lim_f0(f:R->R)(x:Rbar): Lim (fun t => (Finite 0)) p_infty = (Finite 0).
apply Lim_const.
Qed.

Lemma eq1: forall (f:R->R)(c:R)(w:R), (fun t:R => ((- Derive f t) * exp (c * t) * sin (w * t))%R)=
(fun t:R => ((Derive (fun x => - f x) t) * exp (c * t) * sin (w * t))%R).
intros.
apply fun_eq.
intro.
apply sym_eq.
rewrite Derive_opp.
ring.
Qed.

(* differentiation property of lapalce transform *)
Lemma lap_diff : forall (f:R->R)(s:C),laplace2 (Derive f) s =
 S_CRbar_minus (S_CRbar_mul s (laplace2 f s)) (f (0)%R,(0)%R).
intros.
simpl.
unfold laplace2.
unfold S_CRbar_mul.
destruct s as (c,w).
unfold S_CRbar_minus.
f_equal.
unfold re_lap.
unfold im_lap.
unfold re_int.
unfold im_int.
rewrite <- Lim_scal_l.
rewrite <- Lim_scal_l.
rewrite <- Lim_minus.
unfold ref.
unfold imf.
rewrite RInt_by_parts.
rewrite l_exp_cos_null.
rewrite fmul_ok.
rewrite fmul_ok.
rewrite Rmult_0_r.
rewrite Rmult_0_r.
rewrite cos_0.
rewrite exp_0.
rewrite Rmult_1_r.
rewrite Rmult_1_r.
apply Rbar_minus_pos_eq.
rewrite Rbar_minus_0_r.
apply sym_eq.
rewrite <- Lim_opp.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
rewrite <- RInt_scal.
apply sym_eq.
rewrite <- RInt_opp.
apply sym_eq.
rewrite <- RInt_minus.
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
apply e1.
apply ex_RInt_Reals_1.
apply e1.
apply e2.
apply e2.
apply e4.
apply e2.
apply e2.
unfold im_lap.
unfold re_lap.
unfold im_int.
unfold re_int.
rewrite <- Lim_scal_l.
rewrite <- Lim_scal_l.
rewrite <- Lim_plus.
unfold imf.
unfold ref.
rewrite eq1.
rewrite RInt_by_parts.
rewrite l_exp_sin_null.
rewrite fmul_ok.
rewrite fmul_ok.
rewrite Rmult_0_r.
rewrite Rmult_0_r.
rewrite sin_0.
rewrite exp_0.
rewrite Rmult_0_r.
apply Rbar_minus_pos_eq.
rewrite Rbar_minus_0_r.
apply sym_eq.
rewrite <- Lim_opp.
apply Lim_ext.
intro.
rewrite <- RInt_scal.
rewrite <- RInt_scal.
rewrite <- RInt_plus.
apply sym_eq.
rewrite <- RInt_opp.
apply RInt_ext.
intros.
apply sym_eq.
rewrite Derive_mult.
rewrite Derive_exp.
rewrite Derive_sin.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_sin.
apply ex_RInt_Reals_1.
apply e1.
apply ex_RInt_Reals_1.
apply e1.
apply e2.
apply e2.
apply e3.
apply e2.
apply e2.
Qed.

(* integration property of laplace transform *)
(*laplace (RInt f 0 t) = (/s) * laplace f*)

Definition integral_f (f:R->R): R->R :=
fun t => RInt f 0 t.

Lemma eq2: forall(f:R->R), integral_f f 0%R = 0%R.
unfold integral_f.
intro.
apply RInt_point.
Qed.

(*积分上限函数的导数*)
Axiom Derive_integral_f: forall(f:R->R),
forall y,Derive (integral_f f) y = f y.

Lemma laplace2_ext: forall(f:R->R)(g:R->R)(s:C),
(forall y,f y = g y) -> laplace2 f s = laplace2 g s.
intros.
unfold laplace2.
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
apply H.
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
apply H.
Qed.

Lemma eq3 (f:R->R) (s:C): laplace2 f s = laplace2 (Derive (integral_f f)) s.
apply laplace2_ext.
intro.
apply sym_eq.
apply Derive_integral_f.
Qed.

Lemma eq5: forall(f:R->R)(s:C),
laplace2 (Derive (integral_f f)) s = 
S_CRbar_minus (S_CRbar_mul s (laplace2 (integral_f f) s)) (integral_f f 0%R, 0%R).
intros.
apply lap_diff.
Qed.

Lemma eq7: forall(f:R->R)(s:C),
S_CRbar_minus (S_CRbar_mul s (laplace2 (integral_f f) s)) (integral_f f 0%R, 0%R)=
S_CRbar_minus (S_CRbar_mul s (laplace2 (integral_f f) s)) (0%R, 0%R).
intros.
unfold S_CRbar_minus.
destruct (S_CRbar_mul s (laplace2 (integral_f f) s)) as (a1,a2).
f_equal.
rewrite eq2.
apply Rbar_minus_pos_eq.
tauto.
Qed.

Lemma eq6: forall(f:R->R)(s:C),
laplace2 f s =
S_CRbar_minus (S_CRbar_mul s (laplace2 (integral_f f) s)) (0%R,0%R).
intros.
rewrite <- eq7.
rewrite eq3.
apply eq5.
Qed.

Lemma eq8: forall(f:R->R)(s:C),
S_CRbar_minus (S_CRbar_mul s (laplace2 (integral_f f) s)) (0%R,0%R)=
S_CRbar_mul s (laplace2 (integral_f f) s).
intros.
unfold S_CRbar_minus.
destruct (S_CRbar_mul s (laplace2 (integral_f f) s)) as (a1,a2).
f_equal.
apply Rbar_minus_0_l.
apply Rbar_minus_0_l.
Qed.

Lemma eq9:forall(f:R->R)(s:C),
laplace2 f s =
S_CRbar_mul s (laplace2 (integral_f f) s).
intros.
rewrite <- eq8.
apply eq6.
Qed.

Axiom Rbar_pos_mult_eq: forall(x:Rbar)(y:Rbar)(z:Rbar),
x = y -> Rbar_mult z x = Rbar_mult z y.

Lemma eq10: forall(s:C)(a b:CRbar),
a = b -> S_CRbar_mul s a = S_CRbar_mul s b.
intros.
unfold S_CRbar_mul.
destruct s as (c,w).
destruct a as (a1,a2).
rewrite <- H.
f_equal.
Qed.

Lemma eq11:forall(f:R->R)(s:C),
S_CRbar_mul (/s) (laplace2 f s) =S_CRbar_mul (/s) (S_CRbar_mul s (laplace2 (integral_f f) s)).
intros.
apply eq10.
apply eq9.
Qed.

Lemma eq12:forall(t s :C)(a:CRbar),
S_CRbar_mul t (S_CRbar_mul s a) = S_CRbar_mul (Cmult t s) a.
intros.
unfold S_CRbar_mul.
destruct t as (t1,t2).
destruct s as (c,w).
destruct a as (a1,a2).
unfold Cmult.
f_equal.








Lemma eq13:forall(s:C)(a:CRbar),
S_CRbar_mul (/s) (S_CRbar_mul s a) = a .
intros.
unfold S_CRbar_mul.
destruct a as (a1,a2).
destruct s as (c,w).
unfold Cinv.
f_equal.












(*
Lemma lap_int: forall(f:R->R)(s:C),
laplace2 (integral_f f) s = S_CRbar_mul (/s) (laplace2 f s).
intros.
unfold laplace2.
unfold S_CRbar_mul.
destruct s as (c,w).
unfold Cinv.
f_equal.
*)























































































