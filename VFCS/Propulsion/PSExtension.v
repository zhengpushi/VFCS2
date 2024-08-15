(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension of Propulsion System, all need be verified
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)

Require Export PSModel.



(* ######################################################################### *)
(** * Common Ltac *)

(** Fill the parameters *)
Global Ltac fill_params def :=
  autounfold with fcs in *; (* unfold all predicate *)
  intros;
  unfold def;               (* unfold main equation *)
  try subst.                (* subst parameters *)


(* ######################################################################### *)
(** * BASIC Functions *)

(* ======================================================================= *)
(** ** Environment *)

(** 计算最大载重 *)
Definition get_G_maxload_by_T T' := n_r * T' - G.

Theorem get_G_maxload_by_T_ok T' :
  is_T T' ->
  is_G_maxload (get_G_maxload_by_T T').
Proof. fill_params get_G_maxload_by_T. rewrite G_maxload_def. field. Qed.

(** 计算大气压强 *)
Definition P_a := 
  P_a0 * (Rpower (1 - val_0_0065 * (h / (T0 + T_t))) val_5_2561).

Theorem P_a_ok : is_P_a P_a.
Proof. fill_params P_a. rewrite P_a_def. auto. Qed.

Global Opaque P_a.

(** 空气密度模型, 4.3 *)
Definition rho := (T0 * P_a) / (P_a0 * (T0 + T_t)) * rho0.

Theorem rho_ok : is_rho rho.
Proof. 
  fill_params rho. rewrite rho_def. rewrite <- P_a_ok. auto.
Qed.

Theorem zero_le_rho : 0 < rho.
Proof. rewrite <- rho_ok. auto with fcs. Qed.

Global Hint Resolve zero_le_rho : fcs.

Global Opaque rho.
  

(* ======================================================================= *)
(** ** Propeller *)
  
(** 叶面翼型阻力系数公式。4.7, 4.57 *)
Definition C_d := 
  let r1 := (epsilon * atan (H_p / (PI * D_p)) - alpha0) / (PI * A + K0) in
    C_fd + ((PI * A * K0²) / e) * r1 ².

Theorem C_d_ok : is_C_d C_d.
Proof.
  fill_params C_d. autorewrite with fcs. ra. logic; auto with R fcs.
Qed.

(** 证明其值大于零 *)
Theorem zero_lt_C_d: 0 < N -> 0 < C_d.
Proof.
  intros H1. unfold C_d. unfold Rdiv.
  rewrite <- alpha_def2; rewrite <- alpha_ab_def. gt0.
Qed.
Hint Resolve zero_lt_C_d : fcs.

#[global] Opaque C_d.

(** 可证明 C_T_MODEL 的等价形式 *)
Fact C_T_MODEL_eq : 0 < N -> C_T_MODEL = L / (rho * ((N / 60)² * D_p ^ 4)).
Proof.
  intros. rewrite <- T_by_L; auto with fcs.
  rewrite T_def1. rewrite rho_ok. field. neq0.
Qed.

(** 螺旋桨拉力系数公式。4.6, 4.56 *)
Definition C_T :=
  let r1 := (epsilon * atan (H_p / (PI * D_p)) - alpha0) / (PI * A + K0) in
    (1/4) * (PI ^ 3) * lambda * zeta² * B_p * K0 * r1.

Theorem C_T_ok : 0 < N -> is_C_T C_T.
Proof.
  fill_params C_T. rewrite C_T_MODEL_eq; auto.
  autorewrite with fcs. compute. rewrite rho_ok. field. neq0.
Qed.

(* Global Hint Resolve C_T_ok : fcs. *)

(** 证明其值大于零 *)
Theorem zero_le_C_T : 0 < N -> 0 < C_T.
Proof.
  intros. unfold C_T. gt0.
  rewrite <- alpha_def2. rewrite <- alpha_ab_def. gt0.
Qed.

Hint Resolve zero_le_C_T : fcs.
#[global] Opaque C_T.

(** 可证明 C_M_MODEL 的等价形式 *)
Fact C_M_MODEL_eq : 0 < N -> C_M_MODEL = M / (rho * ((N / 60)² * D_p ^ 5)).
Proof. intros. rewrite M_def1. rewrite rho_ok. field. neq0. Qed.

(** 螺旋桨转矩系数公式。4.6, 4.56 *)
Definition C_M := (1 / (8 * A)) * PI² * C_d * zeta² * lambda * B_p².
  
(* 为何产生了 0 < N 的这个条件 ？ *)
Theorem C_M_ok : 0 < N -> is_C_M C_M.
Proof.
  fill_params C_M. rewrite <- C_d_ok. rewrite C_M_MODEL_eq; auto.
  rewrite M_def2. autorewrite with fcs.
  rewrite rho_ok. compute. field. neq0.
Qed.

(** 证明其值大于零 *)
Theorem Rge0_C_M : 0 < N -> 0 < C_M.
Proof.
  intros. unfold C_M. gt0.
Qed.

Global Hint Resolve Rge0_C_M : fcs.

Global Opaque C_M.

(** 由螺旋桨转速计算螺旋桨拉力 *)
Definition get_T_by_N N' := 
  C_T * rho * (N' / 60)² * (D_p ^ 4).

Theorem get_T_by_N_ok N' :
  0 < N' ->
  is_N N' ->
  is_T (get_T_by_N N').
Proof.
  fill_params get_T_by_N. rewrite T_def1.
  rewrite <- C_T_ok; auto.
  rewrite <- rho_ok; auto.
Qed.

(** 由螺旋桨旋转角速度计算螺旋桨拉力 *)
Definition get_T_by_propAngv propAngv' := c_T * (propAngv' * propAngv').

Theorem get_T_by_propAngv_ok propAngv' :
  0 < propAngv' ->
  is_propAngv propAngv' ->
  is_T (get_T_by_propAngv propAngv').
Proof.
  intros. pose proof (get_T_by_N_ok N). unfold is_propAngv, is_T, is_N in *.
  rewrite N_by_propAngv in H1. unfold get_T_by_N, get_T_by_propAngv in *.
  rewrite c_T_def. subst. rewrite H1; auto.
  - rewrite rho_ok. rewrite C_T_ok; auto. ra.
    apply propAngv_gt0_imply_N_gt0; auto.
  - gt0.
Qed.

(** 由螺旋桨转速计算螺旋桨扭矩 *)
Definition get_M_by_N (N' : R) := C_M * rho * (N' / 60)² * (D_p ^ 5).

Theorem get_M_by_N_ok N' :
  0 < N' ->
  is_N N' ->
  is_M (get_M_by_N N').
Proof.
  fill_params get_M_by_N. rewrite M_def1. rewrite rho_ok.
  rewrite C_M_ok; auto. 
Qed.

(** 由螺旋桨旋转角速度计算螺旋桨扭矩 *)
Definition get_M_by_propAngv propAngv' := c_M * (propAngv' * propAngv').

Theorem get_M_by_propAngv_ok propAngv' :
  0 < propAngv' ->
  is_propAngv propAngv' ->
  is_M (get_M_by_propAngv propAngv').
Proof.
  intros. pose proof (get_M_by_N_ok N). unfold is_propAngv, is_M, is_N in *.
  rewrite N_by_propAngv in H1. unfold get_M_by_N, get_M_by_propAngv in *.
  rewrite c_M_def. subst. rewrite H1; auto.
  - rewrite rho_ok. rewrite C_M_ok; auto. ra.
    apply propAngv_gt0_imply_N_gt0; auto.
  - gt0.
Qed.

(** 由螺旋桨拉力计算螺旋桨转速 *)
Definition get_N_by_T T' := 
  60 * sqrt (T' /(rho * C_T * (D_p ^ 4))).

Theorem get_N_by_T_ok T' :
  is_T T' ->
  0 < N ->
  is_N (get_N_by_T T').
Proof.
  fill_params get_N_by_T. rewrite T_def1 in *.
  match goal with
  | |- _ = _ * sqrt (?a) => replace a with (N/60)²
  end.
  - rewrite sqrt_Rsqr. field. ge0.
  - rewrite <- C_T_ok; auto. rewrite rho_ok. rewrite C_T_ok;auto. field. neq0.
Qed.

(** 由螺旋桨扭矩计算螺旋桨转速 *)
Definition get_N_by_M M' := 60 * (sqrt (M' / (rho * (D_p ^ 5) * C_M))).

Theorem get_N_by_M_ok M' :
  is_M M' ->
  0 < N ->
  is_N (get_N_by_M M').
Proof.
  fill_params get_N_by_M. rewrite M_def1.
  match goal with
  | |- _ = _ * sqrt (?a) => replace a with (N/60)²
  end.
  - rewrite sqrt_Rsqr. field. ge0.
  - rewrite <- C_M_ok; auto. rewrite rho_ok. rewrite C_M_ok;auto. field. neq0.
Qed.

(** 由螺旋桨转矩计算螺旋桨推力 *)
Definition get_T_by_M M' := (C_T * M') / (D_p * C_M).

Theorem get_T_by_M_ok M' :
  0 < N ->
  0 < M ->
  is_M M' ->
  is_T (get_T_by_M M').
Proof.
  fill_params get_T_by_M. rewrite (get_T_by_N_ok (get_N_by_M M)).
  - unfold get_T_by_N, get_N_by_M.
    replace (60 * sqrt (M / (rho * D_p ^ 5 * C_M)) / 60)² with
      (M / (rho * D_p ^ 5 * C_M)).
    + rewrite <- C_M_ok;auto. rewrite <- C_T_ok;auto.
      unfold Rsqr. rewrite <- rho_ok. rewrite C_M_ok;auto. field. neq0.
    + unfold Rdiv. rewrite Rinv_r_simpl_m.
      * rewrite Rsqr_sqrt. field. neq0. ge0.
      * lra.
  - unfold get_N_by_M. gt0.
  - apply get_N_by_M_ok; auto. easy.
Qed.

(** 由螺旋桨推力计算螺旋桨转矩 *)
Definition get_M_by_T T' := (C_M * D_p * T') / C_T.

Theorem get_M_by_T_ok T' :
  0 < N ->
  0 < M ->
  is_T T' ->
  is_M (get_M_by_T T').
Proof.
  fill_params get_M_by_T. rewrite (get_T_by_M_ok M); auto; try easy.
  unfold get_T_by_M. field. neq0.
Qed.


(* ======================================================================= *)
(** ** Battery *)

(** 4.17 根据电调输入电流计算电池输出电流 *)
Definition get_I_b_by_I_e I_e' := n_r * I_e' + I_other.

Theorem get_I_b_by_I_e_ok I_e' :
  is_I_e I_e' ->
  is_I_b (get_I_b_by_I_e I_e').
Proof. fill_params get_I_b_by_I_e. rewrite I_b_def. field. Qed.

(** 4.22 根据电池输出电流计算电池续航时间 *)
Definition get_T_b_by_I_b I_b' := (C_b - C_min) / I_b' * val_0_06.

Theorem get_T_b_by_I_b_ok I_b' : 
  is_I_b I_b' ->
  is_T_b (get_T_b_by_I_b I_b').
Proof.
  autounfold with fcs.
  intros. unfold get_T_b_by_I_b. rewrite T_b_def. subst. field. neq0.
Qed.


(* ======================================================================= *)
(** ** Motor *)

(** N_m0 表达式 *)
Definition N_m0 := K_V0 * U_m0.

Theorem N_m0_ok : is_N_m0 N_m0.
Proof. fill_params N_m0. rewrite N_m0_def. auto. Qed.

Theorem ge0_N_m0 : 0 < N_m0.
Proof. rewrite <- N_m0_ok. auto with fcs. Qed.

Global Hint Resolve ge0_N_m0 : fcs.

Global Opaque N_m0.

(** K_E 表达式 *)
Definition K_E := (U_m0 - I_m0 * R_m) / N_m0.

Theorem K_E_ok : is_K_E K_E.
Proof. fill_params K_E. rewrite U_m0_def. rewrite N_m0_ok. field. neq0. Qed.

Theorem ge0_K_E : 0 < K_E.
Proof. rewrite <- K_E_ok. auto with fcs. Qed.

Global Hint Resolve ge0_K_E : fcs.

Global Opaque K_E.

(** K_T 表达式 *)
Definition K_T := 
  (val_9_55 * (U_m0 - I_m0 * R_m)) / (K_V0 * U_m0).

Theorem K_T_ok : is_K_T K_T.
Proof.
  fill_params K_T.
  rewrite K_T_and_K_E. rewrite U_m0_def at 1. rewrite N_m0_def. field.
  auto with R fcs.
Qed.

(** 证明其值大于零 *)
Lemma ge0_K_T : 0 < K_T.
Proof. rewrite <- K_T_ok. rewrite K_T_and_K_E. gt0. Qed.

Global Hint Resolve 
  ge0_K_T
  : fcs.

Global Opaque K_T.

(** 4.11 由扭螺旋桨矩来计算 电机等效输入电流 *)
Definition get_I_m_by_M M' := M' / K_T + I_m0.

Theorem get_I_m_by_M_ok M' :
  is_M M' ->
  is_I_m (get_I_m_by_M M').
Proof.
  fill_params get_I_m_by_M. rewrite motor_model_I.
  rewrite I_0_hat_def. f_equal. rewrite M_def4. rewrite K_T_ok. field. neq0.
Qed.

Definition get_I_m_by_M_direct M' :=
  ((M' * K_V0 * U_m0) / (val_9_55 * (U_m0 - I_m0 * R_m))) + I_m0.

Theorem get_I_m_by_M_direct_ok M' :
  is_M M' ->
  is_I_m (get_I_m_by_M_direct M').
Proof.
  fill_params get_I_m_by_M_direct. 
  rewrite motor_model_I. rewrite I_0_hat_def. f_equal.
  rewrite M_def4. rewrite K_T_and_K_E. rewrite U_m0_def at 2.
  replace (K_E * N_m0 + I_m0 * R_m - I_m0 * R_m) with (K_E * N_m0).
  - rewrite N_m0_def. rewrite K_E_ok. field. neq0. ring_simplify. gt0.
  - field.
Qed.

(** 由螺旋桨推力计算电机等效输入电流 *)
Definition get_I_m_by_T T' := (C_M * D_p * T') / (K_T * C_T) + I_m0.

Theorem get_I_m_by_T_ok T' :
  0 < N ->
  0 < M ->
  is_T T' ->
  is_I_m (get_I_m_by_T T').
Proof.
  fill_params get_I_m_by_T. rewrite (get_I_m_by_M_ok (get_M_by_T T)).
  - unfold get_I_m_by_M, get_M_by_T. field. neq0.
  - apply get_M_by_T_ok; try easy.
Qed.

(** 由螺旋桨转速计算电机等效输入电流 *)
Definition get_I_m_by_N N' := C_M * rho * (N' / 60)² * (D_p ^ 5) / K_T + I_m0.

Theorem get_I_m_by_N_ok N' :
  0 < N' ->
  is_N N' ->
  is_I_m (get_I_m_by_N N').
Proof.
  fill_params get_I_m_by_N. rewrite (get_I_m_by_M_ok (get_M_by_N N)).
  - compute. field. neq0.
  - apply get_M_by_N_ok; try easy.
Qed.

(** 4.10 由扭螺旋桨矩和螺旋桨转速来计算 电机等效输入电压 *)
Definition get_U_m_by_M_and_N M' N' := 
  (((M' * K_V0 * U_m0) / (val_9_55 * (U_m0 - I_m0 * R_m))) + I_m0) * R_m +
  ((U_m0 - I_m0 * R_m) / (K_V0 * U_m0)) * N'.

Theorem get_U_m_by_M_and_N_ok M' N' :
  is_M M' ->
  is_N N' ->
  is_U_m (get_U_m_by_M_and_N M' N').
Proof.
  fill_params get_U_m_by_M_and_N.
  rewrite motor_model_U. rewrite E_a_def. fold (get_I_m_by_M_direct M).
  rewrite (get_I_m_by_M_direct_ok M); auto with fcs.
  replace ((U_m0 - I_m0 * R_m) / (K_V0 * U_m0)) with K_E.
  - rewrite K_E_ok. field.
  - rewrite U_m0_def at 1. rewrite K_E_ok. rewrite N_m0_def. field. neq0.
Qed.

(** 由电机输入电流计算电机转矩 *)
Definition get_M_by_I_m I_m' := K_T * (I_m' - I_m0).

Theorem get_M_by_I_m_ok I_m' :
  is_I_m I_m' ->
  is_M (get_M_by_I_m I_m').
Proof.
  fill_params get_M_by_I_m. rewrite M_def4. rewrite motor_model_I.
  rewrite I_0_hat_def. rewrite K_T_ok. field.
Qed.

(** 根据螺旋桨转速计算反电动势 *)
Definition get_E_a_by_N N' := K_E * N'.
  
Theorem get_E_a_by_N_ok N' :
  is_N N' ->
  is_E_a (get_E_a_by_N N').
Proof. fill_params get_E_a_by_N. rewrite E_a_def. rewrite K_E_ok. auto. Qed.

(** 根据螺旋桨推力计算反电动势 *)
Definition get_E_a_by_T T' := 60 * K_E * sqrt (T' / (rho * C_T * (D_p ^ 4))).

Theorem get_E_a_by_T_ok T' :
  0 < N ->
  is_T T' ->
  is_E_a (get_E_a_by_T T').
Proof.
  fill_params get_E_a_by_T. rewrite (get_E_a_by_N_ok (get_N_by_T T)).
  - unfold get_E_a_by_N, get_N_by_T.
    rewrite <- C_T_ok; auto. field.
  - apply get_N_by_T_ok; try easy.
Qed.

(** 根据螺旋桨转矩计算反电动势 *)
Definition get_E_a_by_M M' := K_E * 60 * sqrt (M' / (rho * D_p ^ 5 * C_M)).

Theorem get_E_a_by_M_ok M' :
  0 < N ->
  is_M M' ->
  is_E_a (get_E_a_by_M M').
Proof.
  fill_params get_E_a_by_M. rewrite (get_E_a_by_N_ok (get_N_by_M M)).
  - unfold get_E_a_by_N, get_N_by_M.
    rewrite <- C_M_ok;auto. compute. field.
  - apply get_N_by_M_ok; try easy.
Qed.

(** 根据反电动势和电机输入电流计算电机输入电压 *)
Definition get_U_m_by_E_a_and_I_m E_a' I_m' := E_a' + R_m * I_m'.

Theorem get_U_m_by_E_a_and_I_m_ok E_a' I_m' :
  is_E_a E_a' ->
  is_I_m I_m' ->
  is_U_m (get_U_m_by_E_a_and_I_m E_a' I_m').
Proof. fill_params get_U_m_by_E_a_and_I_m. rewrite motor_model_U. auto. Qed.

(** 根据螺旋桨转速和螺旋桨扭矩计算电机输入电压 *)
Definition get_U_m_by_N_and_M N' M' := K_E * N' + R_m * (M' / K_T + I_m0).

Theorem get_U_m_by_N_and_M_ok N' M' :
  is_N N' ->
  is_M M' ->
  is_U_m (get_U_m_by_N_and_M N' M').
Proof.
  fill_params get_U_m_by_N_and_M.
  rewrite (get_U_m_by_E_a_and_I_m_ok (get_E_a_by_N N) (get_I_m_by_M M)).
  - compute. field. neq0.
  - apply get_E_a_by_N_ok; try easy.
  - apply get_I_m_by_M_ok; try easy.
Qed.

(** 根据螺旋桨转速计算电机输入电压 *)
Definition get_U_m_by_N N' := 
  K_E * N' + R_m 
  * ((C_M * rho * ((N' / 60) ^ 2) * (D_p ^ 5)) 
  / K_T + I_m0).

Theorem get_U_m_by_N_ok N' :
  0 < N' ->
  is_N N' ->
  is_U_m (get_U_m_by_N N').
Proof.
  fill_params get_U_m_by_N.
  rewrite (get_U_m_by_E_a_and_I_m_ok (get_E_a_by_N N) (get_I_m_by_N N)).
  - compute. field. neq0.
  - apply get_E_a_by_N_ok; try easy.
  - apply get_I_m_by_N_ok; try easy.
Qed.

(** 根据螺旋桨转矩计算电机输入电压 *)
Definition get_U_m_by_M M' := 60 * K_E * (sqrt (M' / (rho * (D_p ^ 5) * C_M))) 
  + R_m * (M' / K_T + I_m0).

Theorem get_U_m_by_M_ok M' :
  0 < N ->
  is_M M' ->
  is_U_m (get_U_m_by_M M').
Proof.
  fill_params get_U_m_by_M.
  rewrite (get_U_m_by_E_a_and_I_m_ok (get_E_a_by_M M) (get_I_m_by_M M)).
  - compute. field. neq0.
  - apply get_E_a_by_M_ok; try easy.
  - apply get_I_m_by_M_ok; try easy.
Qed.

(** 根据螺旋桨推力计算电机输入电压 *)
Definition get_U_m_by_T T' := 
  60 * K_E * sqrt (T' / (rho * C_T * (D_p ^ 4)))
  + R_m * ((C_M * D_p * T') / (K_T * C_T) + I_m0).

Theorem get_U_m_by_T_ok T' :
  0 < N ->
  0 < M ->
  is_T T' ->
  is_U_m (get_U_m_by_T T').
Proof.
  fill_params get_U_m_by_T. 
  rewrite (get_U_m_by_E_a_and_I_m_ok (get_E_a_by_T T) (get_I_m_by_T T)).
  - compute. field. neq0.
  - apply get_E_a_by_T_ok; try easy.
  - apply get_I_m_by_T_ok; try easy.
Qed.

(** 根据电机输入电压和电机输入电流计算电机输出电压 *)
Definition get_U_eo_by_U_m_and_I_m U_m' I_m' := U_m' + I_m' * R_e.

Theorem get_U_eo_by_U_m_and_I_m_ok U_m' I_m' :
  is_U_m U_m' ->
  is_I_m I_m' ->
  is_U_eo (get_U_eo_by_U_m_and_I_m U_m' I_m').
Proof. fill_params get_U_eo_by_U_m_and_I_m. rewrite U_eo_def. auto. Qed.

(** 根据油门指令计算电机输出电压 *)
Definition get_U_eo_by_sigma_e sigma_e' := sigma_e' * U_b.

Theorem get_U_eo_by_sigma_e_ok sigma_e' :
  is_sigma_e sigma_e' ->
  is_U_eo (get_U_eo_by_sigma_e sigma_e').
Proof. fill_params get_U_eo_by_sigma_e. rewrite sigma_e_def. field. neq0. Qed.

(** 根据反电动势和电机输入电流计算电机输出电压 *)
Definition get_U_eo_by_E_a_and_I_m E_a' I_m' := E_a' + (R_m + R_e) * I_m'.

Theorem get_U_eo_by_E_a_and_I_m_ok E_a' I_m' :
  is_E_a E_a' ->
  is_I_m I_m' ->
  is_U_eo (get_U_eo_by_E_a_and_I_m E_a' I_m').
Proof. 
  fill_params get_U_eo_by_E_a_and_I_m. rewrite U_eo_def.
  rewrite motor_model_U. field.
Qed.

(** 根据电机转速计算电机输出电压 *)
Definition get_U_eo_by_N N' := ((R_m + R_e) * C_M * rho * (D_p ^ 5))
  / (K_T * (60 ^ 2)) * (N' ^ 2) + K_E * N' + (R_m + R_e) * I_m0.

Theorem get_U_eo_by_N_ok N' :
  0 < N' ->
  is_N N' ->
  is_U_eo (get_U_eo_by_N N').
Proof. 
  fill_params get_U_eo_by_N.
  rewrite (get_U_eo_by_E_a_and_I_m_ok (get_E_a_by_N N) (get_I_m_by_N N)).
  - compute; field. neq0.
  - apply get_E_a_by_N_ok; try easy.
  - apply get_I_m_by_N_ok; try easy.
Qed.

(** 4.19 根据油门和电机输入电流计算电调输入电流 *)
Definition get_I_e_by_sigma_e_and_I_m sigma_e' I_m' := sigma_e' * I_m'.

Theorem get_I_e_by_sigma_e_and_I_m_ok sigma_e' I_m' :
  is_sigma_e sigma_e' ->
  is_I_m I_m' ->
  is_I_e (get_I_e_by_sigma_e_and_I_m sigma_e' I_m').
Proof. fill_params get_I_e_by_sigma_e_and_I_m. rewrite I_e_def. field. Qed.

(** 4.20 根据电池输入电流计算电调输入电压 *)
Definition get_U_e_by_I_b I_b' := U_b - I_b' * R_b.

Theorem get_U_e_by_I_b_ok I_b' :
  is_I_b I_b' ->
  is_U_e (get_U_e_by_I_b I_b').
Proof. fill_params get_U_e_by_I_b. rewrite U_e_def. field. Qed.


(* ======================================================================= *)
(** ** ESC *)

(** 根据电机转速、螺旋桨扭矩和电池电流计算系统效率 *)
Definition get_eta_by_M_and_N_and_I_b M' N' I_b' :=
  ((2 * PI) / 60) * n_r * M' * N' / (U_b * I_b').

Theorem get_eta_by_M_and_N_and_I_b_ok M' N' I_b' :
  is_M M' ->
  is_N N' ->
  is_I_b I_b' ->
  is_eta (get_eta_by_M_and_N_and_I_b M' N' I_b').
Proof. 
  fill_params get_eta_by_M_and_N_and_I_b. rewrite eta_def. field. neq0.
Qed.

(** 4.18 根据电机等效输入电压和电流计算电调油门 *)
Definition get_sigma_e_by_U_m_and_I_m U_m' I_m' := 
  (U_m' + I_m' * R_e) / U_b.

Theorem get_sigma_e_by_U_m_and_I_m_ok U_m' I_m' :
  is_U_m U_m' ->
  is_I_m I_m' ->
  is_sigma_e (get_sigma_e_by_U_m_and_I_m U_m' I_m').
Proof. 
  fill_params get_sigma_e_by_U_m_and_I_m. rewrite sigma_e_def, U_eo_def. 
  field. neq0.
Qed.

(** 根据电机反电动势和等效输入电流计算电调油门 *)
Definition get_sigma_e_by_E_a_and_I_m E_a' I_m' := 
  (E_a' + (R_m + R_e) * I_m') / U_b.

Theorem get_sigma_e_by_E_a_and_I_m_ok E_a' I_m' :
  is_E_a E_a' ->
  is_I_m I_m' ->
  is_sigma_e (get_sigma_e_by_E_a_and_I_m E_a' I_m').
Proof. 
  fill_params get_sigma_e_by_E_a_and_I_m.
  rewrite (get_sigma_e_by_U_m_and_I_m_ok 
    (get_U_m_by_E_a_and_I_m E_a I_m) I_m); try easy.
  - compute; field. neq0.
  - apply get_U_m_by_E_a_and_I_m_ok; try easy.
Qed.


(* ======================================================================= *)
(** ** Global *)

(** 根据螺旋桨推力计算最大负载 *)
Definition get_G_maxload T' := T' * n_r - G.

Theorem get_G_maxload_ok T' :
  is_T T' ->
  is_G_maxload (get_G_maxload T').
Proof.
  fill_params get_G_maxload. rewrite G_maxload_def. auto.
Qed.

(** 根据螺旋桨推力计算最大俯仰角 *)
Definition get_theta_max T' := acos (G / (n_r * T')).

Theorem get_theta_max_ok T' :
  is_T T' ->
  is_theta_max (get_theta_max T').
Proof.
  fill_params get_theta_max. rewrite theta_max_def. auto.
Qed.

(** 多旋翼的阻力系数 *)
(* 
Definition C_D1 := 
 *)


(* ######################################################################### *)
(** * COMPOSED Functions *)

(** 根据电机反电动势计算计算螺旋桨转速 *)
Definition get_N_by_E_a E_a' := E_a' / K_E_MODEL.

Theorem get_N_by_E_a_ok E_a' :
  is_E_a E_a' ->
  is_N (get_N_by_E_a E_a').
Proof.
  fill_params get_N_by_E_a. rewrite E_a_def. field. neq0.
Qed.

(** 根据反电动势和电机等效输入电流计算电调输入电流 *)
Definition get_I_e_by_E_a_and_I_m E_a' I_m' := 
  ((E_a' + (R_m + R_e) * I_m') * I_m') / U_b.

Theorem get_I_e_by_E_a_and_I_m_ok E_a' I_m' :
  is_E_a E_a' ->
  is_I_m I_m' ->
  is_I_e (get_I_e_by_E_a_and_I_m E_a' I_m').
Proof.
  fill_params get_I_e_by_E_a_and_I_m.
  rewrite (get_I_e_by_sigma_e_and_I_m_ok (get_sigma_e_by_E_a_and_I_m E_a I_m) 
    I_m); try easy.
  - compute; field. neq0.
  - apply get_sigma_e_by_E_a_and_I_m_ok; try easy.
Qed.

(** 根据螺旋桨推力计算电调输入电流 *)
Definition get_I_e_by_T T' := (((60 * K_E * sqrt (T' / (rho * C_T * (D_p ^ 4)))) 
  + (R_m + R_e) * ((C_M * D_p * T') / (K_T * C_T) + I_m0)) 
  * ((C_M * D_p * T') / (K_T * C_T) + I_m0)) / U_b.

Theorem get_I_e_by_T_ok T' :
  0 < N ->
  0 < M ->
  is_T T' ->
  is_I_e (get_I_e_by_T T').
Proof.
  fill_params get_I_e_by_T.
  rewrite (get_I_e_by_E_a_and_I_m_ok (get_E_a_by_T T) (get_I_m_by_T T)); 
    try easy.
  - apply get_E_a_by_T_ok; try easy.
  - apply get_I_m_by_T_ok; try easy.
Qed.

(** 由电调输入电流计算电调输入电压 *)
Definition get_U_e_by_I_e I_e' := U_b - (n_r * I_e' + I_other) * R_b.

Theorem get_U_e_by_I_e_ok I_e' :
  is_I_e I_e' ->
  is_U_e (get_U_e_by_I_e I_e').
Proof.
  fill_params get_U_e_by_I_e.
  rewrite (get_U_e_by_I_b_ok (get_I_b_by_I_e I_e)); try easy.
  apply get_I_b_by_I_e_ok; try easy.
Qed.

(** 由电调输入电流计算电池续航时间 *)
Definition get_T_b_by_I_e I_e := (C_b - C_min) / (n_r * I_e + I_other) 
  * val_0_06.

Theorem get_T_b_by_I_e_ok I_e' :
  is_I_e I_e' ->
  is_T_b (get_T_b_by_I_e I_e').
Proof.
  fill_params get_T_b_by_I_e.
  rewrite (get_T_b_by_I_b_ok (get_I_b_by_I_e I_e)); try easy.
  apply get_I_b_by_I_e_ok; try easy.
Qed.

(** 由电机等效输入电压计算电机转速 *)
Definition get_N_by_U_m U_m' :=
  (1800 * K_T) / (R_m * C_M * rho * (D_p ^ 5)) * (-K_E + sqrt((K_E ^ 2) 
  - (R_m * C_M * rho * (D_p ^ 5) * (R_m * I_m0 - U_m')) / (900 * K_T) )).

Theorem get_N_by_U_m_ok U_m' :
  is_U_m U_m' ->
  is_N (get_N_by_U_m U_m').
Proof.
  fill_params get_N_by_U_m.
(*   erewrite (get_N_by_E_a_ok E_a); auto with fcs. *)
(*   Search U_m. *)
  rewrite (get_U_m_by_N_ok N); auto with fcs.
  - remember (sqrt _).
    pose (1800 * K_T / (N * (R_m * C_M * rho * D_p ^ 5)) + K_E) as r1.
    assert (r² = r1).
    + subst. rewrite Rsqr_sqrt.
      * unfold r1. unfold get_U_m_by_N. ring_simplify.
        remember (R_m * C_M * rho * D_p ^ 5) as r2.
        
(*   rewrite (get_U_m_by_N_ok N); try easy.
  compute.
  field.
  Print get_U_m_by_N.
  Search U_m.
  rewrite (get_N_by_ (get_T_b_by_I_b_ok (get_I_b_by_I_e I_e)); try easy.
  apply get_I_b_by_I_e_ok; try easy.
Qed.
 *)
Admitted.

(** 由电调输出电压计算电机转速 *)
Definition get_N_by_U_eo U_eo' :=
  (1800 * K_T) / ((R_m + R_e) * C_M * rho * (D_p ^ 5)) 
  * (-K_E + sqrt((K_E ^ 2) 
  - ((R_m + R_e) * C_M * rho * (D_p ^ 5)) / (900 * K_T)
  * ((R_m + R_e) * I_m0 - U_eo'))).

Theorem get_N_by_U_eo_ok U_eo' :
  is_U_eo U_eo' ->
  is_N (get_N_by_U_eo U_eo').
Proof.
  fill_params get_N_by_U_eo.
Admitted.

(** 由俯仰角计算平飞速度 *)

