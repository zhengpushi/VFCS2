(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2nd-order homogeneous linear differential equation
              二阶常系数齐次线性微分方程
  author    : Zhengpu Shi
  date      : 2024.05

  remark    :
  1. Solve equation such as: y''(x) + ay'(x) + by(x) = 0

 *)

Require Export DEbase.


(* ######################################################################### *)
(** * General solution of 2nd-order homogeneouse linear differential equation *)

(** Equation: y''(x) + ay'(x) + by(x) = 0 *)
Record Eqn := {
    a : R;
    b : R;
  }.
Notation "e .a" := (a e) (at level 20, format "e .a").
Notation "e .b" := (b e) (at level 20, format "e .b").

(** The solution y(x) satisfy the equation *)
Definition isSolution (e : Eqn) (y : R -> R) : Prop :=
  y '' +f (e.a s* y ') +f (e.b s* y) = fzero.

(* The characteristic polynomial is: r * r + a * r + b,
     and there are three cases for the solutions, depending on the discriminant
     D = a * a - 4 * b. *)

(** Discriminant *)
Definition D (e : Eqn) : R := e.a * e.a - 4 * e.b.

(* ======================================================================= *)
(** ** The general solution when D > 0 *)

(* If D > 0, the characteristic polynomial has two distinct real roots r1 and r2,
     and the general solution is: c_{1}e^{r_{1}x} + c_{2}e^{r_{2}x}. *)
Module Dgt0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Assume D > 0 *)
    Hypotheses HDgt0 : D e > 0.

    (** The root of the characteristic polynomial *)
    Definition r1 : R := (- e.a + sqrt (D e)) / 2.
    Definition r2 : R := (- e.a - sqrt (D e)) / 2.
    
    (** The general solutions *)
    Definition y (c1 c2 : R) := fun x => c1 * exp (r1 * x) + c2 * exp (r2 * x).
    (** 1st derivative of the solution *)
    Definition dy (c1 c2 : R) := fun x => c1 * r1 * exp(r1 * x) + c2 * r2 * exp(r2 * x).
    (** 2st derivative of the solution *)
    Definition d2y (c1 c2 : R) :=
      fun x => c1 * r1 * r1 * exp(r1 * x) + c2 * r2 * r2 * exp(r2 * x).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : forall c1 c2, (y c1 c2)' = dy c1 c2.
    Proof.
      intros. extensionality x. unfold dy,y,r1,r2.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : forall c1 c2, (dy c1 c2)' = d2y c1 c2.
    Proof.
      intros. extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : forall c1 c2, (y c1 c2)'' = d2y c1 c2.
    Proof. intros. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : forall c1 c2, isSolution e (y c1 c2).
    Proof.
      intros. hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,r1,r2,D in *. destruct e; simpl in *.
      field_simplify.
      rewrite pow2_sqrt; try lra.
    Qed.
  End solution.
End Dgt0.

(* ======================================================================= *)
(** ** The general solution when D = 0 *)

(* If D = 0, the characteristic polynomial has a double root −a/2, and the
     general solution is: (c_{1}+c_{2}x) e^{-ax/2}. *)
Module Deq0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Assume D = 0 *)
    Hypotheses HDeq0 : D e = 0.

    (** The root of the characteristic polynomial *)
    Definition r : R := - e.a / 2.
    
    (** The general solutions *)
    Definition y (c1 c2 : R) := fun x => (c1 + c2 * x) * exp (r * x).
    (** 1st derivative of the solution *)
    Definition dy (c1 c2 : R) := fun x => (c2 + r * c1 + r * c2 * x) * exp (r * x).
    (** 2st derivative of the solution *)
    Definition d2y (c1 c2 : R) :=
      fun x => (r * c2 + r * c2 + r * r * c1 + r * r * c2 * x) * exp (r * x).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : forall c1 c2, (y c1 c2)' = dy c1 c2.
    Proof.
      intros. extensionality x. unfold dy,y,r.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : forall c1 c2, (dy c1 c2)' = d2y c1 c2.
    Proof.
      intros. extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : forall c1 c2, (y c1 c2)'' = d2y c1 c2.
    Proof. intros. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : forall c1 c2, isSolution e (y c1 c2).
    Proof.
      intros. hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,r,D in *. destruct e; simpl in *.
      field_simplify.
      replace (a0 ^ 2) with (4 * b0); try lra.
    Qed.
  End solution.
End Deq0.

(* ======================================================================= *)
(** ** The general solution when D < 0 *)

(* If D < 0, the characteristic polynomial has two complex conjugate roots
     r1,r2 = {\alpha} \pm i{\beta}, and the general solution is:
     e^{{\alpha}x}(c_1\cos{\beta x} + c_2\sin{\beta x}). *)
Module Dlt0.
  Section solution.
    (* Give an equation *)
    Variable e : Eqn.
    
    (* Assume D < 0 *)
    Hypotheses HDlt0 : D e < 0.

    (** The root of the characteristic polynomial *)
    Definition alpha := (- e.a)/2.
    Definition beta := (sqrt (- (D e))) / 2.
    Definition r1 : C := alpha +i beta.
    Definition r2 : C := alpha +i (- beta).
    
    (** The general solutions *)
    Definition y (c1 c2 : R) :=
      fun x => exp (alpha * x) *
                 (c1 * cos (beta * x)
                  + c2 * sin (beta * x)).
    
    (** 1st derivative of the solution *)
    Definition dy (c1 c2 : R) :=
      fun x => exp (alpha * x) *
                 (c1 * alpha * cos (beta * x)
                  + c2 * alpha * sin (beta * x)
                  - c1 * beta * sin (beta * x) 
                  + c2 * beta * cos (beta * x)).
    (** 2st derivative of the solution *)
    Definition d2y (c1 c2 : R) :=
      fun x => exp (alpha * x) *
                 (c1 * alpha * alpha * cos (beta * x)
                  + c2 * alpha * alpha * sin (beta * x)
                  - c1 * alpha * beta * sin (beta * x) 
                  + c2 * alpha * beta * cos (beta * x)
                  - c1 * alpha * beta * sin (beta * x)
                  + c2 * alpha * beta * cos (beta * x)
                  - c1 * beta * beta * cos (beta * x)
                  - c2 * beta * beta * sin (beta * x)).
    
    (** verify that: y' = dy *)
    Lemma d_y_eq_dy : forall c1 c2, (y c1 c2)' = dy c1 c2.
    Proof.
      intros. extensionality x. unfold dy,y,alpha,beta.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: dy' = d2y *)
    Lemma d_dy_eq_d2y : forall c1 c2, (dy c1 c2)' = d2y c1 c2.
    Proof.
      intros. extensionality x. unfold dy,d2y.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (** verify that: y'' = d2y *)
    Lemma d2_y_eq_d2y : forall c1 c2, (y c1 c2)'' = d2y c1 c2.
    Proof. intros. rewrite d_y_eq_dy. rewrite d_dy_eq_d2y. auto. Qed.
    
    (** The solution satisfy the equation *)
    Theorem y_spec : forall c1 c2, isSolution e (y c1 c2).
    Proof.
      intros. hnf.
      (* eliminate derivative operations *)
      rewrite d2_y_eq_d2y, d_y_eq_dy.
      (* eliminate function equality *)
      feq.
      (* simplify *)
      unfold d2y,dy,y,alpha,beta,D in *. destruct e; simpl in *.
      field_simplify.
      rewrite pow2_sqrt; try lra.
    Qed.
  End solution.
End Dlt0.


(* Test OCaml extraction *)
(* Extraction HomoLDE2. *)

(* Test *)
Section test.

  (* A simple example shows three cases D > 0, D = 0, and D < 0 *)
  Section three_cases.
    (* when D > 0 *)

    (* Give an equation *)
    Let e1 : Eqn := {| a := 3; b := 1 |}. (* D = 3 * 3 - 4 * 1 = 5 *)
    (* Compute its solution *)
    (* Eval cbv in Dgt0.y e1. *)
    (* Verify the solution *)
    Goal forall c1 c2, isSolution e1 (Dgt0.y e1 c1 c2).
    Proof. intros. apply Dgt0.y_spec. cbv. lra. Qed.

    (* when D = 0 *)
    Let e2 : Eqn := {| a := 2; b := 1 |}. (* D = 2 * 2 - 4 * 1 = 0 *)
    (* Eval cbv in Deq0.y e2. *)
    Goal forall c1 c2, isSolution e2 (Deq0.y e2 c1 c2).
    Proof. intros. apply Deq0.y_spec. cbv. lra. Qed.

    (* when D < 0 *)
    Let e3 : Eqn := {| a := 2; b := 3 |}. (* D = 2 * 2 - 4 * 3 = - 8 *)
    (* Eval cbv in Dlt0.y e3. *)
    Goal forall c1 c2, isSolution e3 (Dlt0.y e3 c1 c2).
    Proof. intros. apply Dlt0.y_spec. cbv. lra. Qed.
  End three_cases.

  (* eg 12.4.2, XuXiaoZhan,page336 *)
  Section eg12_4_2.
    (* verify the solution *)
    Let e : Eqn := {| a := 2; b := 1|}.
    Goal forall c1 c2, Deq0.y e c1 c2 = fun x => c1 * exp (- x) + c2 * x * exp (- x).
    Proof.
      intros. cbv. extensionality x. field_simplify.
      f_equal; f_equal; f_equal; field.
    Qed.
    
  End eg12_4_2.

  (* eg3, https://www.math.ncue.edu.tw/~kwlee/ODEBoyce/DEChapter3.pdf, page43 *)
  (* 弹簧震动的最简单的型式：简谐运动 *)
  Section vibrating_springs_Simple_Harmonic_Motion.

    (* m y'' + k y = 0
       ==> y'' + 0 * y' + k/m y = 0 *)
    Variable m k : R.
    Hypotheses Hm_gt0 : m > 0.
    Hypotheses Hk_gt0 : k > 0.
    
    Let e : Eqn := {| a := 0; b := k/m|}.

    (* characteristic equation: mr^2 + k = 0,
       the solution of it is: r = ±(ω0) i, ω0 = √(k/m) *)

    (* The standard form solution *)
    Goal forall c1 c2, isSolution e (Dlt0.y e c1 c2).
    Proof.
      apply Dlt0.y_spec. cbv. ring_simplify.
      replace (-4 * k * / m) with ((-4) * (k/m)) by lra.
      assert (k / m > 0); try lra. ra.
    Qed.

    (* Some physical concepts *)

    (* two arbitrary numbers for general solution *)
    Variable c1 c2 : R.
    Hypothesis Hc1c2_neq0 : c1 * c1 + c2 * c2 <> 0.
    
    Let omega0 := sqrt (k/m).   (* frenquency, 频率 *)
    Let Amp := sqrt (c1 * c1 + c2 * c2). (* amplitude, 振幅 *)
    Variable delta : R.                  (* phase angle, 相角 *)
    Hypothesis H_sin_delta : sin delta = c2 / Amp.
    Hypothesis H_cos_delta : cos delta = c1 / Amp.
    Let T := (2 * PI) / omega0. (* period, 周期 *)

    (* The friendly form solution *)
    Let sol := fun t => c1 * cos (omega0 * t) + c2 * sin (omega0 * t).
    (* Verify that sol is equal to y *)
    Goal sol = Dlt0.y e c1 c2.
    Proof.
      cbv. extensionality t. ring_simplify. ra.
      repeat f_equal.
      - rewrite (sqrt_mult _ (k/m)); ra. rewrite Rabs_right; ra.
      - rewrite (sqrt_mult _ (k/m)); ra. rewrite Rabs_right; ra.
    Qed.

    (* The friendly form solution (another one) *)
    Let sol' := fun t => Amp * cos (omega0 * t - delta).
    (* Verify that sol' is equal to sol *)
    Goal sol' = sol.
    Proof.
      extensionality t. unfold sol', sol.
      rewrite cos_sub. rewrite H_sin_delta, H_cos_delta.
      field_simplify; auto.
      unfold Amp. apply sqrt_neq0_iff. ra.
    Qed.
  End vibrating_springs_Simple_Harmonic_Motion.

  (* eg3, https://www.math.ncue.edu.tw/~kwlee/ODEBoyce/DEChapter3.pdf, page43 *)
  (* 弹簧的阻尼自由振动 *)
  Section vibrating_springs_Damped_Free_Vibration.

    (* m y'' + g y' + k y = 0 *)
    Variable m g k : R.
    Hypotheses Hm_gt0 : m > 0.
    Hypotheses Hg_gt0 : g > 0.
    Hypotheses Hk_gt0 : k > 0.
    
    Let e : Eqn := {| a := g/m; b := k/m|}.

    (* overdamping, 过阻尼，(g*g - 4*m*k > 0)
       此时，r1 < 0, r2 < 0，所以当 t -> 0 时， e^{r1t} -> 0, e^{r2t} -> 0。
       从图像上看，系统终将稳定。
       即使阻力过大，也至多造成一次振荡。*)
    Section overdamping.
      Hypotheses Hmgk : g * g - 4 * m * k > 0.

      (* delta > 0 *)
      Goal D e > 0.
      Proof. cbv. field_simplify; ra. Qed.

      (* c1*e^{r1t} + c2*e^{r2t} *)
      (* Eval cbv in Dgt0.y e. *)
    End overdamping.
    
    (* critical damping，临界阻尼，(g*g - 4*m*k = 0) *)
    Section critical.
      Hypotheses Hmgk : g * g - 4 * m * k = 0.

      (* delta = 0 *)
      Goal D e = 0.
      Proof.
        cbv. field_simplify; ra.
        replace (g ^ 2) with (g * g); ra. rewrite Hmgk. ra.
      Qed.

      (* c1*e^{r*t} + c2*x*e^{r*t} *)
      (* Eval cbv in Deq0.y e. *)
    End critical.
    
    (* underdamping，低阻尼，(g*g - 4*m*k < 0) *)
    Section underdamping.
      Hypotheses Hmgk : g * g - 4 * m * k < 0.

      (* delta < 0 *)
      Goal D e < 0.
      Proof.
        cbv. field_simplify; ra.
      Qed.

      (* c1*e^{(-r/2m)*t} * (c1*cos(u*t) + c2*sin(u*t)),
         u = sqrt(4km*g*g)/(2*m) *)
      (* Eval cbv in Dlt0.y e. *)
    End underdamping.
  End vibrating_springs_Damped_Free_Vibration.

End test.
