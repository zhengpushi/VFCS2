Require Import Reals.
Open Scope R_scope.

Definition fadd (f:R->R) (g:R->R) (t:R) : R := f t + g t.
Definition fminus (f:R->R) (g:R->R) (t:R) : R := f t - g t.
Definition fmul (f:R->R) (g:R->R) (t:R) : R := f t * g t.
Definition fdiv (f:R->R) (g:R->R) (t:R) : R := f t / g t.
Definition fconst (c:R)(f:R->R)(t:R)   : R := c *(f t).
Definition fopp (f:R->R)(t:R) : R := - f t.

Infix "+f" := fadd (at level 50,  left associativity)  : R_scope.
Infix "-f" := fminus (at level 55, left associativity) : R_scope.
Infix "*f" := fmul (at level 43,  left associativity)  : R_scope.
Infix "/f" := fdiv (at level 46, left associativity) : R_scope.
Infix "*c" := fconst (at level 40) : R_scope.

Lemma fadd_ok : forall (u v : R->R) (t : R),
  (u +f v) t = u t + v t.
intros. reflexivity.
Qed.

Lemma fminus_ok : forall (u v : R->R) (t : R),
  (u -f v) t = u t - v t.
Proof.
intros. reflexivity.
Qed.

Lemma fmul_ok : forall (u v : R->R) (t : R),
  (u *f v) t = u t * v t.
Proof.
intros. reflexivity.
Qed.

Lemma fdiv_ok : forall (u v : R->R) (t : R),
  (u /f v) t = u t / v t.
Proof.
intros. reflexivity.
Qed.

Lemma fconst_ok : forall (c:R) (u : R->R) (t : R),
  (c *c u) t = c * u t.
Proof.
intros. reflexivity.
Qed.

Lemma fopp_ok : forall (u :R->R)(t : R),
(fopp u) t = - u t.
Proof.
intros. reflexivity.
Qed.

Axiom fun_eq : forall (u v :R->R), 
   (forall t, u t = v t) -> u = v.

Lemma fadd_assoc : forall (u v w : R->R),  u +f (v +f w) = (u +f v) +f w.
intros u v w.
apply fun_eq.
intro t.
repeat rewrite fadd_ok.
ring.
Qed.

Lemma fmul_assoc : forall (u v w : R->R),  u *f (v *f w) = (u *f v) *f w.
intros u v w.
apply fun_eq.
intro t.
repeat rewrite fmul_ok.
ring.
Qed.

Lemma fadd_sym : forall (u v: R->R),  u +f v = v +f u.
intros u v.
apply fun_eq.
intro t.
repeat rewrite fadd_ok.
ring.
Qed.

Lemma fmul_sym : forall (u v: R->R),  u *f v = v *f u.
intros u v.
apply fun_eq.
intro t.
repeat rewrite fmul_ok.
ring.
Qed.

Lemma fconst2_assoc : forall (c d : R) (w : R->R),  c *c (d *c w) = (c * d) *c w.
intros c d w.
apply fun_eq.
intro t.
repeat rewrite fconst_ok.
ring.
Qed.

Lemma fconst1_assoc : forall (c : R) (v w : R->R),  c *c (v *f w) = (c *c v) *f w.
intros c v w.
apply fun_eq.
intro t.
rewrite fconst_ok.
repeat rewrite fmul_ok.
rewrite fconst_ok.
ring.
Qed.































































