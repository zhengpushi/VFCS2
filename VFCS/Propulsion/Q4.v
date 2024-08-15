(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Model of Question 4
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)

Require Import PSExtension.


(** Solve maximum speed and distance at flatFlying mode *)
Section Q4.
  
  Definition the_State := FlatFlying.
  
  Hypothesis arg_State : is_State the_State.
  
  Variable the_theta : R.
  
  Hypothesis arg_theta : is_theta the_theta.
  Hypothesis thete_range : 0 < the_theta < PI/2.
  
  Lemma cos_the_theta_gt0 : 0 < cos the_theta.
  Proof. apply cos_gt_0; lra. Qed.
  
  (** 4.40 *)
  Definition the_V := sqrt ((2 * G * tan the_theta) / 
    (rho * S * 
      (C_D1 * (1 - (sin the_theta)^3) + C_D2 * (1 - (cos the_theta)^3)))).

  Lemma the_V_ok : 0 < V -> is_V the_V.
  Proof.
    fill_params the_V.
    rewrite <- C_D_def.
    rewrite Rmult_assoc. rewrite <- flatfly_hori; auto.
    rewrite F_drag_def; auto. rewrite rho_ok.
    match goal with
    | |- ?a = sqrt (?b) => replace b with (a)²
    end.
    - rewrite sqrt_Rsqr; auto. ge0.
    - unfold Rsqr. field. neq0.
  Qed.
  
  (** 4.41 *)
  Definition the_N := 60 * sqrt (G / (rho * C_T * D_p ^ 4 * n_r 
    * cos the_theta)).
  
  Lemma the_N_ok : 0 < N -> is_N the_N.
  Proof.
    intros.
    autounfold with fcs in *. unfold the_N.
    rewrite (get_N_by_T_ok T);auto with fcs.
    unfold get_N_by_T. rewrite flatfly_vert;auto. f_equal. f_equal.
    rewrite arg_theta. field. neq0. apply cos_the_theta_gt0.
  Qed.
  
  (** 4.42 *)
  Definition the_M := (G * C_M * D_p) / (C_T * n_r * cos the_theta).
  
  Lemma the_M_ok : 
    0 < N ->
    0 < M ->
    is_M the_M.
  Proof.
    intros.
    autounfold with fcs in *. unfold the_M.
    rewrite (get_M_by_T_ok T); auto with fcs.
    rewrite flatfly_vert; auto. unfold get_M_by_T.
    rewrite arg_theta. field. neq0. apply cos_the_theta_gt0.
  Qed.
  
  (** 4.43 *)
  Definition the_U_m := get_U_m_by_M_and_N the_M the_N.
  
  Definition the_I_m := get_I_m_by_M the_M.
  
  Definition the_sigma_e := get_sigma_e_by_U_m_and_I_m the_U_m the_I_m.
  
  Definition the_I_e := get_I_e_by_sigma_e_and_I_m the_sigma_e the_I_m.
  
  Definition the_I_b := get_I_b_by_I_e the_I_e.
  
  Definition the_T_b := get_T_b_by_I_b the_I_b.
  
  (** 4.44 *)
  Definition the_Z := 60 * the_T_b * the_V.
  
End Q4.
