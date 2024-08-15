(* diffferential equations on function vectors. *)
Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
From Coquelicot Require Import Rcomplements Rbar Hierarchy.
From Coquelicot Require Import Compactness Lim_seq Derive.
Require Import laplace_chen4_rbar.
Require Import complex2.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Derive.
Require Import functional.
Require Import FunctionalExtensionality.
Require Import matrix2.
Open Scope type_scope.

(* polymorphic matrix2 *)
(*Section Generic_Matrix2.*)

(*2017/8/24*)

(* 二阶函数向量 *)
Definition CF2 := (C->C) * (C->C).

Open Scope R_scope.


(*将laplace推广到二维向量*)
Definition laplace_v2 (fv:RF2)(s:C): CV2 :=
let (f1,f2) := fv in
(laplace f1 s, laplace f2 s).

Definition lap_left_v2 (fv:RF2)(s:C): Prop :=
let (f,g) := fv in
lap_left f s /\ lap_left g s.

Definition lap_right_v2(fv:RF2)(s:C): Prop :=
let (f,g) := fv in
lap_right f s /\ lap_right g s.

Definition ex_derive_RF2 (fv:RF2): Prop :=
let (f,g) := fv in
(forall x, ex_derive f x) /\ (forall x, ex_derive g x).

Definition ex_finite_lim_re_v2 (fv:RF2)(s:C):Prop :=
let (f,g) := fv in
ex_finite_lim (ref f s) p_infty /\
ex_finite_lim (ref g s) p_infty.

Definition is_lim_re_v2 (fv:RF2)(s:C):Prop :=
let (f,g) := fv in
is_lim (ref f s) p_infty 0 /\
is_lim (ref g s) p_infty 0.

Definition ex_finite_lim_im_v2 (fv:RF2)(s:C):Prop :=
let (f,g) := fv in
ex_finite_lim (imf f s) p_infty /\
ex_finite_lim (imf g s) p_infty.

Definition is_lim_im_v2 (fv:RF2)(s:C):Prop :=
let (f,g) := fv in
is_lim (imf f s) p_infty 0 /\
is_lim (imf g s) p_infty 0.



(*二维向量 laplace的微分性质*)
Lemma laplace_v2_diff: forall(fv:RF2)(s:C),
lap_left_v2 fv s -> lap_right_v2 fv s ->
ex_derive_RF2 fv ->
lap_left_v2 (derive_RV2 fv) s ->
lap_right_v2 (derive_RV2 fv) s ->
ex_finite_lim_re_v2 fv s -> is_lim_re_v2 fv s ->
ex_finite_lim_im_v2 fv s -> is_lim_im_v2 fv s ->
laplace_v2 (derive_RV2 fv) s = CV2_minus (C_CV2_mul s (laplace_v2 fv s )) 
(RF2_app fv 0).
destruct fv as (f,g).
destruct s as (c,w).
intros.
simpl.
f_equal.
rewrite lap_diff1.
simpl.
f_equal.
apply H.
apply H0.
unfold ex_derive_RF2 in H1.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H5.
apply H6.
apply H7.
rewrite lap_diff1.
simpl.
f_equal.
apply H.
apply H0.
unfold derivable.
intro.
apply ex_derive_Reals_0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H5.
apply H6.
apply H7.
Qed.


(* L[AX(t)] = AX(s)*)
Lemma lap_v2_const: forall(X:RF2)(A:RM2)(s:C),
lap_left_v2 X s ->
lap_right_v2 X s ->
laplace_v2 (RF2_cmul A X) s = CMV2_cmul A (laplace_v2 X s).
destruct X as (f,g).
destruct s as (c,w).
destruct A as ((a1,a2),(a3,a4)).
intros.
simpl.
f_equal.
rewrite lap_line.
simpl.
f_equal.
apply H.
apply H.
apply H0.
apply H0.
rewrite lap_line.
simpl.
f_equal.
apply H.
apply H.
apply H0.
apply H0.
Qed.

(*L[X + U] = L[X] + L[U]*)
Lemma lap_v2_plus: forall(X:RF2)(U:RF2)(s:C),
lap_left_v2 X s ->
lap_right_v2 X s ->
lap_left_v2 U s ->
lap_right_v2 U s ->
laplace_v2 (RF2_plus X U) s = CV2_add  (laplace_v2 X s) (laplace_v2 U s).
destruct X as (x1,x2).
destruct U as (u1,u2).
destruct s as (c,w).
intros.
simpl.
f_equal.
rewrite lap_plus.
simpl.
f_equal.
apply H.
apply H1.
apply H0.
apply H2.
rewrite lap_plus.
simpl.
f_equal.
apply H.
apply H1.
apply H0.
apply H2.
Qed.


(*ex_finite_lim
  (fun b : R =>
   RInt (fun t : R => (a1 *c f +f a2 *c g) t * exp (- c * t) * cos (w * t)) 0 b)
  p_infty *)

Lemma lap_c_left_v2_pre: forall(f g:R->R)(a1 a2 c w:R),
continuity f -> continuity g ->
(fun b : R =>RInt (fun t : R => (a1 *c f +f a2 *c g) t * exp (- c * t) * cos (w * t)) 0 b) = 
(fun b => (a1 * RInt (fun t => (f t * exp (- c * t) * cos (w * t))%R) 0 b)%R) +f
(fun b => (a2 * RInt (fun t => (g t * exp (- c * t) * cos (w * t))%R) 0 b)%R).
intros.
extensionality t.
rewrite fplus_ok.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite fplus_ok.
rewrite ? fconst_ok.
ring.
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
apply H0.
apply continuity_exp.
apply continuity_cos.
Qed.

(* the real part existence precondition of vector laplace *)
Lemma lap_c_left_v2: forall(A:RM2)(X:RF2)(s:C),
lap_left_v2 X s -> lap_left_v2 (RF2_cmul A X) s.
destruct A as ((a1,a2),(a3,a4)).
destruct X as (f,g).
destruct s as (c,w).
intros.
simpl.
split.
split.
apply continuity_plus.
apply continuity_scal.
unfold lap_left_v2 in H.
apply H.
apply continuity_scal.
unfold lap_left_v2 in H.
apply H.
rewrite lap_c_left_v2_pre.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
apply H.
apply H.
apply H.
split.
apply continuity_plus.
apply continuity_scal.
apply H.
apply continuity_scal.
apply H.
rewrite lap_c_left_v2_pre.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
apply H.
apply H.
apply H.
Qed.

(*ex_finite_lim
  (fun b : R => RInt (fun t : R => - (a1 *c f +f a2 *c g) t * exp (- c * t) * sin (w * t)) 0 b)
  p_infty*)
Lemma lap_c_right_v2_pre: forall(f g:R->R)(a1 a2 c w:R),
continuity f -> continuity g ->
(fun b : R =>RInt (fun t : R => - (a1 *c f +f a2 *c g) t * exp (- c * t) * sin (w * t)) 0 b) = 
(fun b => (a1 * RInt (fun t => (- f t * exp (- c * t) * sin (w * t))%R) 0 b)%R) +f
(fun b => (a2 * RInt (fun t => (- g t * exp (- c * t) * sin (w * t))%R) 0 b)%R).
intros.
extensionality t.
rewrite fplus_ok.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
apply RInt_ext.
intros.
rewrite fplus_ok.
rewrite ? fconst_ok.
ring.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_opp.
apply H.
apply continuity_exp.
apply continuity_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_opp.
apply H0.
apply continuity_exp.
apply continuity_sin.
Qed.

(*the imaginary part existence precondition of vector laplace*)
Lemma lap_c_right_v2: forall(A:RM2)(X:RF2)(s:C),
lap_right_v2 X s -> lap_right_v2 (RF2_cmul A X) s.
destruct A as ((a1,a2),(a3,a4)).
destruct X as (f,g).
destruct s as (c,w).
intros.
simpl.
split.
split.
apply continuity_plus.
apply continuity_scal.
unfold lap_right_v2 in H.
apply H.
apply continuity_scal.
unfold lap_right_v2 in H.
apply H.
rewrite lap_c_right_v2_pre.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
apply H.
apply H.
apply H.
split.
apply continuity_plus.
apply continuity_scal.
apply H.
apply continuity_scal.
apply H.
rewrite lap_c_right_v2_pre.
apply ex_finite_lim_plus.
apply ex_finite_lim_scal_l.
apply H.
apply ex_finite_lim_scal_l.
apply H.
apply H.
apply H.
Qed.

(*ex_finite_lim
  (fun b : R =>
   RInt (fun t : R => (x1 +f y1) t * exp (- c * t) * cos (w * t)) 0 b)
  p_infty*)
(*lap_left_v2 (RF2_plus (RF2_cmul A X) (RF2_cmul B U)) s*)
Lemma lap_left_plus_pre: forall(x1 y1:R->R)(c w:R),
continuity x1 -> continuity y1 ->
(fun b : R =>RInt (fun t : R => (x1 +f y1) t * exp (- c * t) * cos (w * t)) 0 b)=
(fun b : R =>RInt (fun t : R => x1 t * exp (- c * t) * cos (w * t)) 0 b) +f
(fun b : R =>RInt (fun t : R => y1 t * exp (- c * t) * cos (w * t)) 0 b).
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

(*the real part addition existence *)
Lemma lap_left_plus: forall(X Y:RF2)(s:C),
lap_left_v2 X s ->
lap_left_v2 Y s ->
lap_left_v2 (RF2_plus X Y) s.
destruct X as (x1,x2).
destruct Y as (y1,y2).
destruct s as (c,w).
intros.
simpl.
split.
split.
apply continuity_plus.
apply H.
apply H0.
rewrite lap_left_plus_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
split.
apply continuity_plus.
apply H.
apply H0.
rewrite lap_left_plus_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
Qed.

(*ex_finite_lim (fun b : R => RInt (fun t : R => - (x1 +f y1) t * exp (- c * t) * sin (w * t)) 0 b)
  p_infty*)
Lemma lap_right_plus_pre: forall(x1 y1:R->R)(c w:R),
continuity x1 ->continuity y1 ->
(fun b : R => RInt (fun t : R => - (x1 +f y1) t * exp (- c * t) * sin (w * t)) 0 b)  =
(fun b : R => RInt (fun t : R => - x1 t * exp (- c * t) * sin (w * t)) 0 b) +f
(fun b : R => RInt (fun t : R => - y1 t * exp (- c * t) * sin (w * t)) 0 b).
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

Lemma lap_right_plus: forall(X Y:RF2)(s:C),
lap_right_v2 X s ->
lap_right_v2 Y s ->
lap_right_v2 (RF2_plus X Y) s.
destruct X as (x1,x2).
destruct Y as (y1,y2).
destruct s as (c,w).
intros.
simpl.
split.
split.
apply continuity_plus.
apply H.
apply H0.
rewrite lap_right_plus_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
split.
apply continuity_plus.
apply H.
apply H0.
rewrite lap_right_plus_pre.
apply ex_finite_lim_plus.
apply H.
apply H0.
apply H.
apply H0.
Qed.



(*L[AX + BU] = A*L[X] + B*L[U]*)
Lemma lap_v2_line: forall(A:RM2)(B:RM2)(X:RF2)(U:RF2)(s:C),
lap_left_v2 X s ->
lap_right_v2 X s ->
lap_left_v2 U s ->
lap_right_v2 U s ->
laplace_v2 (RF2_plus (RF2_cmul A X) (RF2_cmul B U)) s = CV2_add  
(CMV2_cmul A (laplace_v2 X s)) (CMV2_cmul B (laplace_v2 U s)).
intros.
rewrite <- lap_v2_const.
rewrite <- lap_v2_const.
apply lap_v2_plus.
apply lap_c_left_v2.
assumption.
apply lap_c_right_v2.
assumption.
apply lap_c_left_v2.
assumption.
apply lap_c_right_v2.
assumption.
assumption.
apply H2.
assumption.
apply H0.
Qed.

(* X=Y -> L[X] = L[Y]*)
Lemma laplace_v2_ext: forall(X Y:RF2)(s:C),
X = Y ->
lap_left_v2 X s ->
lap_right_v2 X s ->
lap_left_v2 Y s ->
lap_right_v2 Y s ->
laplace_v2 X s = laplace_v2 Y s.
destruct X as (f1,f2).
destruct Y as (g1,g2).
destruct s as (c,w).
intros.
rewrite H.
(*trival用于左右一样的时候*)
trivial.
Qed.

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

(* r - 0 = r *)
Lemma CV2_minus_0_r: forall(a:CV2),
CV2_minus a (0%C,0%C) = a.
intro.
destruct a as (a1,a2).
simpl.
f_equal.
carith1 a1.
carith1 a2.
Qed.

(*r1 + r2 - r1 = r2*)
Lemma CV2_plus_minus: forall r1 r2:CV2, CV2_minus (CV2_add r1 r2) r1 = r2.
intros.
destruct r1 as (r11,r12).
destruct r2 as (r21,r22).
simpl.
f_equal.
carith2 r11 r21.
carith2 r12 r22.
Qed.

(*r1=r2 -> r1 - r = r2 - r*)
Lemma CV2_minus_eq_compat_r: forall r1 r2 r:CV2, 
r1 = r2 -> CV2_minus r1 r = CV2_minus r2 r.
intros.
destruct r1 as (r11,r12).
destruct r2 as (r21,r22).
destruct r  as (r01,r02).
simpl.
f_equal.
apply pair_eq in H.
elim H.
intros.
rewrite H0.
tauto.
apply pair_eq in H.
elim H.
intros.
rewrite H1.
tauto.
Qed.

(*r1 = r2 -> m*r1 = m*r2*)
Lemma CM2_CV2_mul_l: forall(r1 r2:CV2)(m:CM2),
r1 = r2 ->
CMV2_cmul m r1 = CMV2_cmul m r2.
intros.
destruct r1 as (r11,r12).
destruct r2 as (r21,r22).
destruct m as ((m11,m12),(m21,m22)).
simpl.
f_equal.
apply pair_eq in H.
elim H.
intros.
rewrite H0.
rewrite H1.
tauto.
apply pair_eq in H.
elim H.
intros.
rewrite H0.
rewrite H1.
carith4 m21 r21 m22 r22.
Qed.

Open Scope C_scope.

(** add to complex2.v **)
Lemma Cplus_eq_compat_l: forall r r1 r2:C,
r1 = r2 -> r + r1 = r + r2.
intros.
rewrite H.
tauto.
Qed.

Lemma Cplus_eq_compat_r: forall r r1 r2:C,
r1 = r2 -> r1 + r = r2 + r.
intros.
rewrite H.
tauto.
Qed.

(* m * n * r = m * (n * r)*)
Lemma CM2_CV2_assoc: forall(m n :CM2)(r:CV2),
CMV2_cmul (CM2_mul m n) r =CMV2_cmul m (CMV2_cmul n r).
intros.
destruct m as ((m11,m12),(m21,m22)).
destruct n as ((n11,n12),(n21,n22)).
destruct r as (r1,r2).
simpl.
f_equal.
rewrite ? Cmult_plus_distr_r.
rewrite ? Cmult_plus_distr_l.
rewrite <- ? Cmult_assoc.
rewrite ? Cplus_assoc.
apply Cplus_eq_compat_l.
rewrite <- ? Cplus_assoc.
apply Cplus_eq_compat_r.
apply Cplus_comm.
rewrite ? Cmult_plus_distr_r.
rewrite ? Cmult_plus_distr_l.
rewrite <- ? Cmult_assoc.
rewrite ? Cplus_assoc.
apply Cplus_eq_compat_l.
rewrite <- ? Cplus_assoc.
apply Cplus_eq_compat_r.
apply Cplus_comm.
Qed.

(*I * r = r*)
Lemma CMV2_cmul_CM2_unit_l: forall r:CV2,
CMV2_cmul CM2_unit r = r.
intro.
destruct r as (r1,r2).
unfold CM2_unit.
unfold CMV2_cmul.
unfold CV2_dot.
rewrite ? Cmult_0_r.
rewrite ? Cmult_1_r.
rewrite Cplus_0_r.
rewrite Cplus_comm.
rewrite Cplus_0_r.
tauto.
Qed.

(*对e1两边求Laplace变换*)
Lemma lap_e1:
verify_pre X U s ->
laplace_v2 (derive_RV2 X) s = laplace_v2 (RF2_plus (RF2_cmul A X) (RF2_cmul B U)) s.
intros.
apply laplace_v2_ext.
apply e1.
apply H.
apply H.
apply lap_left_plus.
apply lap_c_left_v2.
apply H.
apply lap_c_left_v2.
apply H.
apply lap_right_plus.
apply lap_c_right_v2.
apply H.
apply lap_c_right_v2.
apply H.
Qed.

(*sX(s)-0 = sX(s)*)
Lemma eq_1: RF2_app X 0 = (0%R,0%R)->
CV2_minus (C_CV2_mul s (laplace_v2 X s)) (RF2_app X 0)  = C_CV2_mul s (laplace_v2 X s).
intros.
rewrite H.
apply CV2_minus_0_r.
Qed.

(*sX(s) = AX(s)+BU(s)*)
Lemma eq_2: 
verify_pre X U s ->RF2_app X 0 = (0%R,0%R)->
C_CV2_mul s (laplace_v2 X s) = CV2_add (CMV2_cmul A (laplace_v2 X s))
(CMV2_cmul B (laplace_v2 U s)).
intros.
rewrite <- eq_1.
rewrite <- laplace_v2_diff.
rewrite <- lap_v2_line.
apply lap_e1.
assumption.
apply H. apply H. apply H. apply H. apply H.
apply H. apply H. apply H. apply H. apply H.
apply H. apply H. apply H. assumption.
Qed.

(* (sI-A)X(s) = AX(s) + BU(s) - AX(s) *)
Lemma eq_3: 
verify_pre X U s ->RF2_app X 0 = (0%R,0%R)->
CMV2_cmul (CM2_minus (C_CM2_mul s CM2_unit) A) (laplace_v2 X s)=
CV2_minus (CV2_add (CMV2_cmul A (laplace_v2 X s)) (CMV2_cmul B (laplace_v2 U s)))
(CMV2_cmul A (laplace_v2 X s)).
intros.
rewrite <- CV2_minus_mult_abstract.
apply CV2_minus_eq_compat_r.
apply eq_2.
assumption.
assumption.
Qed.

(* (SI-A)X(s) = BU(s) *)
Lemma eq_4:
verify_pre X U s ->RF2_app X 0 = (0%R,0%R)->
CMV2_cmul (CM2_minus (C_CM2_mul s CM2_unit) A) (laplace_v2 X s)=
(CMV2_cmul B (laplace_v2 U s)).
intros.
rewrite eq_3.
apply CV2_plus_minus.
assumption.
assumption.
Qed.

(*(SI-A)^(-1)(SI-A)X(s) = (SI-A)^(-1) BU(s)*)
Lemma eq_5:
verify_pre X U s ->RF2_app X 0 = (0%R,0%R)->
CM2_det (CM2_minus (C_CM2_mul s CM2_unit) A) <> 0 ->
CMV2_cmul (CM2_inv_full (CM2_minus (C_CM2_mul s CM2_unit) A) )
(CMV2_cmul (CM2_minus (C_CM2_mul s CM2_unit) A) (laplace_v2 X s))=
CMV2_cmul (CM2_inv_full (CM2_minus (C_CM2_mul s CM2_unit) A) ) (CMV2_cmul B (laplace_v2 U s)).
intros.
apply CM2_CV2_mul_l.
apply eq_4.
assumption.
assumption.
Qed.

(*(SI-A)^(-1)(SI-A)X(s) = X(s)*)
Lemma eq_6:
verify_pre X U s ->
CM2_det (CM2_minus (C_CM2_mul s CM2_unit) A) <> 0 ->
CMV2_cmul (CM2_inv_full (CM2_minus (C_CM2_mul s CM2_unit) A) )
(CMV2_cmul (CM2_minus (C_CM2_mul s CM2_unit) A) (laplace_v2 X s))=laplace_v2 X s.
intros.
rewrite <- CM2_CV2_assoc.
rewrite CM2_inv_full_ok.
apply CMV2_cmul_CM2_unit_l.
assumption.
Qed.

(*X(s) = (SI-A)^(-1) BU(s)*)
Lemma eq_7:
verify_pre X U s ->
CM2_det (CM2_minus (C_CM2_mul s CM2_unit) A) <> 0 ->
laplace_v2 X s = 
CMV2_cmul (CM2_inv_full (CM2_minus (C_CM2_mul s CM2_unit) A) ) (CMV2_cmul B (laplace_v2 U s)).
intros.
rewrite <- eq_6.
apply eq_5.
assumption.
assumption.
assumption.
assumption.
Qed.



































