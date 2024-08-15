(* functionals on real functions. *)
Require Import Reals.
Open Scope R_scope.

Axiom fun_eq : forall (u v :R->R), 
    (forall t, u t = v t) -> u = v.


(* functional plus. *)
Definition fplus (u:R->R) (v:R->R) : R->R :=
  fun t => u t + v t.

Definition fminus (u:R->R) (v:R->R) : R->R :=
  fun t => u t - v t.

Definition fconst (c:R) (u:R->R) : R->R :=
  fun t => c * u t.

Definition fmul (u:R->R) (v:R->R) : R->R :=
  fun t => u t * v t.

Definition fdiv (u:R->R) (v:R->R) : R->R :=
  fun t => u t / v t.

Infix "+f" := fplus (at level 50,  left associativity)  : R_scope.
Infix "-f" := fminus (at level 55, left associativity) : R_scope.
Infix "*c" := fconst (at level 40) : R_scope.
Infix "*f" := fmul (at level 43,  left associativity)  : R_scope.
Infix "/f" := fdiv (at level 46, left associativity) : R_scope.

(** functional equalities **)

(* function plus. *)
Lemma fplus_ok : forall (u v : R->R) (t : R),
    (u +f v) t = u t + v t.
Proof.
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

Lemma fplus_assoc : forall (u v w : R->R),
    u +f (v +f w) = (u +f v) +f w.
Proof.
  intros u v w.
  assert(forall t, (u +f (v +f w)) t = ((u +f v) +f w) t).
  intro t. repeat rewrite fplus_ok. ring. apply fun_eq. assumption.
Qed.

Lemma fmul_assoc : forall (u v w : R->R),
    u *f (v *f w) = (u *f v) *f w.
Proof.
  intros u v w.
  assert(forall t, (u *f (v *f w)) t = ((u *f v) *f w) t).
  intro t. repeat rewrite fmul_ok. ring. apply fun_eq. assumption.
Qed.

Lemma fplus_sym : forall (u v: R->R),
    u +f v = v +f u.
Proof.
  intros u v.
  assert(forall t, (u +f v) t = (v +f u) t).
  intro t. repeat rewrite fplus_ok. ring. apply fun_eq. assumption.
Qed.

Lemma fmul_sym : forall (u v: R->R),
    u *f v = v *f u.
Proof.
  intros u v.
  assert(forall t, (u *f v) t = (v *f u) t).
  intro t. repeat rewrite fmul_ok. ring. apply fun_eq. assumption.
Qed.

Lemma fconst2_assoc : forall (c d : R) (w : R->R),
    c *c (d *c w) = (c * d) *c w.
Proof.
  intros.
  assert(forall t, (c *c (d *c w)) t = ((c * d) *c w) t).
  intro t. repeat rewrite fconst_ok. ring. apply fun_eq. assumption.
Qed.

Lemma fconst1_assoc : forall (c : R) (v w : R->R),
    c *c (v *f w) = (c *c v) *f w.
Proof.
  intros.
  assert(forall t, (c *c (v *f w)) t = ((c *c v) *f w) t).
  intro t. repeat (rewrite fconst_ok,fmul_ok). 
  repeat (rewrite fmul_ok,fconst_ok). ring. 
  apply fun_eq. assumption.
Qed.
