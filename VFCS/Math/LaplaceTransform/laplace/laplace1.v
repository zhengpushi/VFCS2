Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
Require Import Psatz.
Open Scope R_scope.

(* Require Import functional. *)
From FinMatrix Require Import Complex.

(* f(x) * e(-ax) * cos(bx) *)
(* s = c + i w *)
Definition ref (f : R->R) (s:C) (t:R) : R :=
 let (c,w) := s in
   f t * exp (-c * t) * cos (w * t).

(* -f(x) * e(-ax) * cos(bx) *)
Definition imf (f : R->R) (s:C) (t:R) : R :=
  let (c,w) := s in
    - f t * exp (-c * t) * sin (w * t).

Check RInt.
Definition re_int f (s:C) (b:R) : R := RInt (ref f s) 0 b.
Definition im_int f (s:C) (b:R) : R := RInt (imf f s) 0 b.

Definition CRbar := (Rbar * Rbar)%type.

(* the two parts of laplace transform of f. *)
Definition re_lap f (s:C) : Rbar := Lim (re_int f s) p_infty.
Definition im_lap f (s:C) : Rbar := Lim (im_int f s) p_infty.

Definition laplace (f:R->R)(s:C) :CRbar
  := (re_lap f s, im_lap f s ).

(* 下面定义四种运算 *)
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
Axiom ex_derive_exp: forall(c:R), derivable (fun t => exp (c * t)).
Axiom ex_derive_cos: forall(c:R), derivable (fun t => cos (c * t)).
Axiom ex_derive_sin: forall(c:R), derivable (fun t => sin (c * t)).

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

(* Coquelicot中定义的两种极限谓词，后者包含极限值正负无穷*)
Lemma ex_finite_ex_lim (f:R->R)(x:Rbar):
ex_finite_lim f x -> ex_lim f x.
intros.
apply ex_finite_lim_correct.
apply H.
Qed.

(*函数f极限存在，那么m*f极限也存在，这里的极限谓词 ex_finite_lim 表示极限值为有限实数*)
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

(*两个有限的实数，他们的和是存在的*)
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

(*如果两个函数的极限值都是有限实数，那么它们的和是存在的*)
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

(*为了证明下面的引理ex_finite_lim_opp，需要将函数变形*)
Lemma ex_finite_lim_opp_pre: forall(f:R->R),
(fun t:R => (- f t)%R) = (fun t:R => ((-1) * (f t))%R).
intro.
apply fun_eq.
intro.
ring.
Qed.

(*函数f的极限值为有限实数，那么（-f）极限值也为有限实数*)
Lemma ex_finite_lim_opp: forall(f:R->R)(x:Rbar),
  ex_finite_lim f x -> ex_finite_lim (fun y => (- f y)%R) x.
intros.
rewrite ex_finite_lim_opp_pre.
apply ex_finite_lim_scal_l.
apply H.
Qed.

(*两个函数的极限值为有限实数，极限值的差也是存在的*)
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

(*为了证明下面的引理lap_c_left,需要将函数变形*)
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

(*函数f实部的积分是收敛的，那么函数(m*f)实部积分也收敛*)
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

(*为了证明下面的引理lap_c_right，需要将函数变形*)
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

(*函数f的虚部积分收敛，那么函数(m*f)虚部积分也收敛*)
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

(*分部积分的形式化,f和g都是可导的，而且导函数都是连续的*)
Axiom RInt_by_parts : forall(f:R->R)(g:R->R),
derivable f  ->
derivable g  ->
continuity (Derive f) ->
continuity (Derive g) ->
Lim (fun b => RInt (fun t:R => ((Derive f t) * (g t))%R ) 0 b) p_infty = Rbar_minus
(Rbar_minus (Lim (f *f g ) p_infty) (Lim (fun b => RInt (fun t:R => ((f t)*(Derive g t ))%R) 0 b) p_infty) )
(Finite ((f *f g) 0%R)).

(*定义两个谓词，用来表示 下面这个函数在正无穷大出的极限值*)
Definition f_lim_0_cos (f:R->R)(s:C):Rbar :=
let (c,w) := s in
Lim (f *f (fun t:R => ((exp (- c * t)) * (cos (w * t)))%R)) p_infty.

Definition f_lim_0_sin (f:R->R)(s:C):Rbar :=
let (c,w) := s in
Lim ((fun x:R => (- f x)%R) *f (fun t:R => ((exp (- c * t)) * (sin (w * t)))%R) ) p_infty.

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
apply fun_eq.
intro.
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

(*定义公理说明指数函数，sin，cos求导之后的结果*)
Axiom Derive_exp: forall(c x :R),
Derive (fun t => exp (c * t)) x = (fun t => (c * exp (c * t))%R) x.
(*为了之后的证明，将上述公理，换一个形式,不包含参数的形式*)
Lemma Derive_exp1: forall(c:R),
Derive (fun t => exp (c * t)) = (fun t => (c * exp (c * t))%R).
intros.
apply fun_eq.
intros.
apply Derive_exp.
Qed.

Axiom Derive_cos: forall(c x :R),
Derive (fun t => cos (c * t)) x = (fun t => (-c * sin (c * t))%R) x.
Lemma Derive_cos1: forall(c:R),
Derive (fun t => cos (c * t))  = (fun t => (-c * sin (c * t))%R).
intros.
apply fun_eq.
intro.
apply Derive_cos.
Qed.

Axiom Derive_sin: forall(c x:R),
Derive (fun t => sin (c * t)) x = (fun t => (c * cos (c * t))%R) x.
Lemma Derive_sin1: forall(c:R),
Derive (fun t => sin (c * t))  = (fun t => (c * cos (c * t))%R).
intros.
apply fun_eq.
apply Derive_sin.
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

(*为了之后的证明，将Coquelicot中的引理Derive引理变形为不包含参数的形式*)
Lemma Derive_opp1: forall(f:R->R),
Derive (fun x:R => (- f x)%R) = opp_fct (Derive f).
intro.
apply fun_eq.
intros.
apply Derive_opp.
Qed.

(*拉普拉斯变换的微分性质*)
(* differentiation property of lapalce transform *)
Lemma lap_diff : forall (f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
derivable f ->
lap_left (Derive f) s ->
lap_right (Derive f) s ->
f_lim_0_cos f s = Finite 0 ->
f_lim_0_sin f s = Finite 0 ->
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
rewrite RInt_by_parts.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite cos_0.
rewrite exp_0.
rewrite ? Rmult_1_r.
apply Rbar_minus_pos_eq.
rewrite H4.
rewrite Rbar_minus_0_r.
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
rewrite Derive_exp.
rewrite Derive_cos.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
apply H6.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
unfold imf.
apply continuity_pt_scal.
apply continuity_pt_mult.
apply continuity_pt_mult.
apply continuity_pt_opp.
elim H.
intros.
apply H6.
apply continuity_exp.
apply continuity_sin.
apply H1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_cos.
elim H2.
intros.
apply H6.
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
unfold ref.
apply ex_lim_scal_l.
apply ex_finite_ex_lim.
elim H.
intros.
apply H7.
apply ex_lim_scal_l.
unfold imf.
elim H0.
intros.
apply ex_finite_ex_lim.
apply H7.
apply ex_finite_minus.
apply ex_finite_lim_scal_l.
unfold ref.
elim H.
intros.
apply H7.
apply ex_finite_lim_scal_l.
unfold imf.
elim H0.
intros.
apply H7.
(*im_lap*)
unfold im_lap.
unfold im_int.
unfold re_lap.
unfold re_int.
rewrite <- ? Lim_scal_l.
rewrite <- Lim_plus.
unfold imf.
rewrite RInt_by_parts_e2.
rewrite RInt_by_parts.
rewrite ? fmul_ok.
rewrite ? Rmult_0_r.
rewrite sin_0.
rewrite exp_0.
rewrite ? Rmult_0_r.
apply Rbar_minus_pos_eq.
unfold f_lim_0_sin in H5.
rewrite H5.
rewrite Rbar_minus_0_r.
rewrite <- Lim_opp.
apply Lim_ext.
intro.
rewrite <- ? RInt_scal.
rewrite <- RInt_plus.
rewrite <- RInt_opp.
apply RInt_ext.
intros.
unfold ref.
rewrite Derive_mult.
rewrite Derive_exp.
rewrite Derive_sin.
ring.
apply ex_derive_Reals_1.
apply ex_derive_exp.
apply ex_derive_Reals_1.
apply ex_derive_sin.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
unfold ref.
apply continuity_pt_mult.
apply continuity_pt_mult.
elim H.
intros.
apply H6.
apply continuity_exp.
apply continuity_cos.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt1.
intro.
apply continuity_pt_scal.
repeat apply continuity_pt_mult.
apply continuity_pt_opp.
elim H.
intros.
apply H6.
apply continuity_exp.
apply continuity_sin.
apply derivable_opp.
apply H1.
apply derivable_mult.
apply ex_derive_exp.
apply ex_derive_sin.
rewrite Derive_opp1.
apply continuity_opp.
elim H2.
intros.
apply H6.
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
apply ex_lim_scal_l.
apply ex_finite_ex_lim.
unfold ref.
elim H.
intros.
apply H7.
apply ex_lim_scal_l.
unfold imf.
apply ex_finite_ex_lim.
elim H0.
intros.
apply H7.
apply ex_finite_plus.
apply ex_finite_lim_scal_l.
unfold ref.
elim H.
intros.
apply H7.
apply ex_finite_lim_scal_l.
unfold imf.
elim H0.
intros.
apply H7.
Qed.


(* integration property of laplace transform *)

Axiom ex_derive_RInt1: forall(f:R->R),
continuity f -> derivable (RInt f 0).
Axiom Derive_RInt1: forall(f:R->R)(y:R),
continuity f ->
Derive (RInt f 0) y = f y.
Lemma Derive_RInt11: forall(f:R->R),
continuity f -> Derive (RInt f 0) = f.
intros.
apply fun_eq.
intros.
apply Derive_RInt1.
assumption.
Qed.

Lemma RInt_f_0_0 (f:R->R): RInt f 0 0 = 0%R.
apply RInt_point.
Qed.


Lemma lap_derive_RInt: forall(f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 ->
f_lim_0_sin (RInt f 0) s = Finite 0 ->
laplace (Derive (RInt f 0)) s = 
S_CRbar_minus (S_CRbar_mul s (laplace (RInt f 0) s)) (RInt f 0 0, 0%R).
destruct s as (c,w).
intros.
apply lap_diff.
apply H1.
apply H2.
apply ex_derive_RInt1.
elim H.
intros.
apply H5.
rewrite Derive_RInt11.
apply H.
elim H.
intros.
apply H5.
rewrite Derive_RInt11.
apply H0.
elim H.
intros.
apply H5.
apply H3.
apply H4.
Qed.


Lemma S_CRbar_minus_0_r: forall(a:CRbar),
S_CRbar_minus a (0%R,0%R) = a.
intro.
unfold S_CRbar_minus.
destruct a as (a1,a2).
rewrite ? Rbar_minus_0_l.
reflexivity.
Qed.


Lemma S_CRbar_minus_eq0: forall (f:R->R)(s:C),
S_CRbar_minus (S_CRbar_mul s (laplace (RInt f 0) s)) (RInt f 0 0 ,0%R)=
S_CRbar_mul s (laplace (RInt f 0) s).
intros.
rewrite RInt_f_0_0.
apply S_CRbar_minus_0_r.
Qed.

Lemma S_CRbar_mul_pos_eq: forall (s:C)(a:CRbar)(b:CRbar),
a = b -> S_CRbar_mul s a = S_CRbar_mul s b.
intros.
rewrite H.
reflexivity.
Qed.

Lemma lap_derive_RInt1: forall(f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 -> 
f_lim_0_sin (RInt f 0) s = Finite 0 ->
laplace (Derive (RInt f 0)) s =  S_CRbar_mul s (laplace (RInt f 0) s).
intros.
rewrite <- S_CRbar_minus_eq0.
apply lap_derive_RInt.
apply H.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
Qed.

Lemma lap_ext_e1 :forall(f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
laplace (Derive (RInt f 0)) s = laplace f s .
intros.
destruct s as (c,w).
rewrite Derive_RInt11.
tauto.
elim H.
intros.
apply H1.
Qed.

Lemma lap_derive_RInt2: forall(f:R->R)(s:C),
lap_left f s ->
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 ->
f_lim_0_sin (RInt f 0) s = Finite 0 ->
laplace f s =  S_CRbar_mul s (laplace (RInt f 0) s).
intros.
rewrite <- lap_ext_e1.
apply lap_derive_RInt1.
apply H.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H.
apply H0.
Qed.

Axiom S_S_CRbar_mul: forall (s :C)(t:C)(a:CRbar),
S_CRbar_mul s (S_CRbar_mul t a) = S_CRbar_mul (s * t) a.
Axiom S_CRbar_1_l: forall (a:CRbar),
S_CRbar_mul 1 a = a.

Lemma lap_derive_RInt3: forall(f:R->R)(s:C),
s<>0 ->
lap_left f s ->
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 ->
f_lim_0_sin (RInt f 0) s = Finite 0 ->
S_CRbar_mul (/s) (S_CRbar_mul s (laplace (RInt f 0) s)) = S_CRbar_mul (/s) (laplace f s).
intros.
apply S_CRbar_mul_pos_eq.
apply sym_eq.
apply lap_derive_RInt2.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H5.
Qed.

Lemma lap_derive_RInt4: forall(f:R->R)(s:C),
s <> 0 ->
lap_left f s -> 
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 ->
f_lim_0_sin (RInt f 0) s = Finite 0 ->
S_CRbar_mul (/s) (S_CRbar_mul s (laplace (RInt f 0) s)) = laplace (RInt f 0) s.
intros.
rewrite S_S_CRbar_mul.
rewrite Cinv_l.
rewrite S_CRbar_1_l.
reflexivity.
apply H.
Qed.


Lemma lap_derive_RInt5: forall(f:R->R)(s:C),
s <> 0 ->
lap_left f s -> 
lap_right f s ->
lap_left (RInt f 0) s ->
lap_right (RInt f 0) s ->
f_lim_0_cos (RInt f 0) s = Finite 0 ->
f_lim_0_sin (RInt f 0) s = Finite 0 ->
laplace (RInt f 0) s =  S_CRbar_mul (/s) (laplace f s).
intros.
rewrite <- lap_derive_RInt4.
apply lap_derive_RInt3.
apply H.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H5.
apply H.
apply H0.
apply H1.
apply H2.
apply H3.
apply H4.
apply H5.
Qed.




















































































































































































