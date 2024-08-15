(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose:    Model of Propulsion System, all theory from text book
  author:     Zhengpu Shi
  date:       2022.11.25

  History:
  1. 2020.12.30, first edition, weak verification.
  2. 2021.05.25, second edition, with Axiom and "is_xx" predication to
     enhance the verification.
  3. 2022.11.25, third edition, with the help of Inductive, to
     seperate every variables, because all variables are R type in last
     version.
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)


From FinMatrix Require Export RExt.

(* (** Generate a real number. eg: makeR 123 100 => 1.23 *) *)
(* Definition makeR : Z -> positive -> R := *)
(*   fun num den => Q2R (Qmake num den). *)


(* ######################################################################### *)
(** * Data structures *)

(** 飞行器状态 *)
Inductive PlaneState : Set :=
  | Hovering    (* 悬停中 *)
  | FlatFlying  (* 平飞，即推力、俯仰角和重力满足一定关系 *)
  | Other       (* 其他 *)
.


(* ######################################################################### *)
(** * Model of Environment *)

Module Env.
  
  (* ======================================================================= *)
  (** ** Constants *)
  Parameter n_r : R.              (* 旋翼数目，单位：无 *)
  Parameter rho0 : R.             (* 标准大气密度，= 1.293 kg/m³ (0℃,273K) *)
  Parameter T0 : R.               (* 温度常数，= 273 K *)
  Parameter P_a0 : R.             (* 标准大气压，= 101325 Pa *)

  (** Real numbers for compatibility with earlier than Coq 8.9,
      and another benefits are:
      1. extract to a float number, rather than a rational expression
      2. avoid mistake when coding with these values everywhere. *)
  Parameter val_0_0065 : R.
  Parameter val_5_2561 : R.

  (* ======================================================================= *)
  (** ** Variables *)

  (* 飞行环境空气密度，单位：kg/m³ *)
  Inductive Rho := mk_Rho (v : R).
  Definition Rho2R (x : Rho) : R := let '(mk_Rho v) := x in v.
  Coercion Rho2R : Rho >-> R.

  (* 大气压强，单位：Pa *)
  Inductive Pa := mk_Pa (v : R).
  Definition Pa2R (x : Pa) : R := let '(mk_Pa v) := x in v.
  Coercion Pa2R : Pa >-> R.

  (* 温度，单位：℃ *)
  Inductive Tt := mk_Tt (v : R).
  Definition Tt2R (x : Tt) : R := let '(mk_Tt v) := x in v.
  Coercion Tt2R : Tt >-> R.
  
  (* 海拔高度，单位：m *)
  Inductive H := mk_H (v : R).
  Definition H2R (x : H) : R := let '(mk_H v) := x in v.
  Coercion H2R : H >-> R.

  (* ======================================================================= *)
  (** ** Assumptions *)
  Hypotheses n_r_gt0 : n_r > 0.

  (* ======================================================================= *)
  (** ** Acceptted Theories *)

  (** 空气密度模型, (4.3) *)
  Inductive Rho_Pa_Tt_spec (rho:Rho) (pa:Pa) (tt:Tt) :=
    Rho_Pa_Tt (_:
        (rho:R) = (T0 * pa) / (P_a0 * (T0 + tt)) * rho0).
                                  
  (** 大气压强模型, (4.4) *)
  Inductive Pa_H_Tt_spec (pa:Pa) (h:H) (tt:Tt) :=
    Pa_H_Tt (_:
        (pa:R) =
          P_a0 * (Rpower (1 - val_0_0065 * (h / (T0 + tt))) val_5_2561)).

End Env.


(* ######################################################################### *)
(** * Model of Propeler *)

Module Ppl.

  (** 导入 Env 模块 *)
  Import Env.
  
  (* ======================================================================= *)
  (** ** Constants *)
  Parameter D_p : R. (* 螺旋桨直径，单位：m *)
  Parameter H_p : R. (* 螺旋桨螺距，单位：m *)
  Parameter theta_p : R. (* 桨叶角，单位：rad *)
  Parameter epsilon : R. (* 下洗效应带来的校正因子，单位: 无，要求为正实数 *)
  Parameter phi0 : R. (* 几何入流角，单位：rad *)
  Parameter alpha : R. (* 有效迎角，单位：rad *)
  Parameter alpha0 : R. (* 零升迎角，单位：rad *)
  Parameter alpha_ab : R. (* 绝对迎角，单位：rad *)
  Parameter K0 : R. (* ?，单位: 无 *)
  Parameter c_p : R. (* 平均几何弦长，单位：m *)
  Parameter A : R. (* 展弦比，单位: 无 *)
  Parameter C1 : R. (* 叶片截面翼型的升力系数，单位: 无 *)
  Parameter C_fd : R. (* 零升阻力系数，单位：无 *)
  Parameter e : R. (* Oswald因子，单位：无 *)
  Parameter B_p : R. (* 桨叶数，单位：无 *)
  Parameter lambda : R. (* 螺旋桨修正系数，单位：无 *)


(* ======================================================================= *)
  (** ** Variables *)
  (* 螺旋桨拉力，单位：N *)
  Inductive T := mk_T (v : R).
  Definition T2R (x : T) : R := let '(mk_T v) := x in v.
  Coercion T2R : T >-> R.

  (* 螺旋桨扭矩，单位：N.m *)
  Inductive M := mk_M (v : R).
  Definition M2R (x : M) : R := let '(mk_M v) := x in v.
  Coercion M2R : M >-> R.

  (* 螺旋桨转速，单位：r/min *)
  Inductive N := mk_N (v : R).
  Definition N2R (x : N) : R := let '(mk_N v) := x in v.
  Coercion N2R : N >-> R.

  (* 叶片截面翼型的阻力系数，单位：无 *)
  Inductive C_d := mk_C_d (v : R).
  Definition C_d2R (x : C_d) : R := let '(mk_C_d v) := x in v.
  Coercion C_d2R : C_d >-> R.

  (* 推力系数, 单位：无 *)
  Inductive C_T := mk_C_T (v : R).
  Definition C_T2R (x : C_T) : R := let '(mk_C_T v) := x in v.
  Coercion C_T2R : C_T >-> R.

  (* 扭矩系数，单位：无 *)
  Inductive C_M := mk_C_M (v : R).
  Definition C_M2R (x : C_M) : R := let '(mk_C_M v) := x in v.
  Coercion C_M2R : C_M >-> R.

  (* 桨叶面积，单位：m² *)
  Inductive S_sa := mk_S_sa (v : R).
  Definition S_sa2R (x : S_sa) : R := let '(mk_S_sa v) := x in v.
  Coercion S_sa2R : S_sa >-> R.

  (* 桨叶上的来流速度，单位：m/s *)
  Inductive W := mk_W (v : R).
  Definition W2R (x : W) : R := let '(mk_W v) := x in v.
  Coercion W2R : W >-> R.

  (* 叶片升力，单位：N *)
  Inductive L := mk_L (v : R).
  Definition L2R (x : L) : R := let '(mk_L v) := x in v.
  Coercion L2R : L >-> R.

  (* zeta，单位：无 *)
  Inductive Zeta := mk_Zeta (v : R).
  Definition Zeta2R (x : Zeta) : R := let '(mk_Zeta v) := x in v.
  Coercion Zeta2R : Zeta >-> R.

  (* 下洗气流引起的阻升角，单位：rad *)
  Inductive Gamma := mk_Gamma (v : R).
  Definition Gamma2R (x : Gamma) : R := let '(mk_Gamma v) := x in v.
  Coercion Gamma2R : Gamma >-> R.

  (* 下洗效应修正角，单位：rad*)
  Inductive Delta := mk_Delta (v : R).
  Definition Delta2R (x : Delta) : R := let '(mk_Delta v) := x in v.
  Coercion Delta2R : Delta >-> R.

  (* ======================================================================= *)
  (** ** Assumptions *)
  Axiom D_p_gt0 : D_p > 0.
  Axiom c_p_gt0 : c_p > 0.
  Axiom K0_gt0 : K0 > 0.
  Axiom e_gt0 : e > 0.
  (* Axiom rho_gt0 : Rho > 0. *)
  Axiom lambda_gt0 : lambda > 0.
  (* Axiom zeta_gt0 : Zeta > 0. *)
  Axiom B_p_gt0 : B_p > 0.
  Axiom alpha_ab_gt0 : alpha_ab > 0.
  Axiom A_gt0 : A > 0.
  Axiom C_fd_gt0 : C_fd > 0.
  Axiom epsilon_gt0 : epsilon > 0.
  (* Axiom cos_gamma_neq0 : cos Gamma <> 0. *)


  (* ======================================================================= *)
  (** ** Acceptted Theories *)

  (** 4.1 螺旋桨拉力计算模型 *)
  Inductive T_CT_Rho_N_spec (t:T) (ct:C_T) (rho:Rho) (n:N) :=
    T_CT_Rho_N (_ :
        (t:R) = ct * rho * (n / 60)² * (D_p ^ 4)).

  (** 4.2 螺旋桨扭矩计算模型 *)
  Inductive M_CM_Rho_N_spec (m:M) (cm:C_M) (rho:Rho) (n:N) :=
    M_CM_Rho_N (_ :
        (m:R) = cm * rho * (n / 60)² * (D_p ^ 5)).

  (** 4.47 桨叶角定义 *)
  Axiom theta_p_def : theta_p = atan (H_p / (PI * D_p)).

  (** 4.48 有效迎角定义 *)
  Axiom alpha_def : alpha = epsilon * (theta_p - phi0).

  (** p78，多旋翼下，几何入流角约等于0 *)
  Axiom phi0_def : phi0 = 0.

  (** 4.49 绝对迎角与有效迎角的关系 *)
  Axiom alpha_ab_def : alpha_ab = alpha - alpha0. 

  (** p78 展弦比的定义 *)
  Axiom A_def : A = D_p / c_p.

  (** 4.50 升力系数与绝对迎角的关系 *)
  Axiom C1_def : C1 = (K0 * alpha_ab) / (1 + K0 / (PI * A)).

  (** p78 桨叶面积定义 *)
  Inductive S_sa_def_spec (ssa:S_sa) :=
    S_sa_def (_ :
        (ssa:R) = B_p * lambda * D_p * c_p / 2).

  (** 4.51 叶片截面翼型的阻力系数定义 *)
  Inductive C_d_def_spec (c_d : C_d) :=
    C_d_def (_ :
        (c_d:R) = C_fd + (1 / (PI * A * e)) * (C1²)).

  (** 4.52 叶片升力定义 *)
  Inductive L_rho_Ssa_W_spec (l:L) (rho:Rho) (ssa:S_sa) (w:W) :=
    L_rho_Ssa_W (_ :
        (l:R) = (1/2) * C1 * rho * ssa * w²).

  (** 4.53 桨叶上的来流速度定义 *)
  Inductive W_Zeta_N_spec (w:W) (zeta:Zeta) (n:N) :=
    W_N (_ :
        (w:R) = PI * zeta * D_p * (n / 60)).

  (** 4.54 由叶素理论建立的螺旋桨拉力模型 *)
  Inductive T_L_Gamma_Delta_spec (t:T) (l:L) (gamma:Gamma) (delta:Delta) :=
    T_L_Gamma_Delta (_ :
        (t:R) = l * (cos (gamma + phi0) / cos (gamma - delta))).

  (** 4.55 螺旋桨扭矩的另一个模型 *)
  Inductive M_Rho_Cd_W_Ssa_spec (m:M) (rho:Rho) (cd:C_d) (w:W) (ssa:S_sa) :=
    M_Rho_Cd_W_Ssa (_ :
        (m:R) = (1/4) * rho * B_p * cd * w² * ssa * D_p).

  (** p79 下洗气流引起的阻生角定义 *)
  Inductive Gamma_Cd_spec (gamma:Gamma) (cd:C_d) :=
    Gamma_Cd (_ :
        (gamma:R) = atan (cd / C1)).

  (** p79 下洗效应修正角可以忽略 *)
  Axiom delta_def : forall (delta:Delta), (delta:R) = 0.

  ? 暂停一下，Inductive对于单变量的关系描述的很好，可是多变量时，
    好像 Axiom 更合适。暂时不知道这么多变量的 Inductive 格式的 relation建立之后，
    如何用于证明性质？

  (** alpha的一个更常用的公式 *)
  Lemma alpha_def2 : alpha = epsilon * atan (H_p * / (PI * D_p)).
  Proof. autorewrite with fcs. unfold Rdiv. field. Qed.

  (** T = L *)
  Lemma T_by_L : cos gamma <> 0 -> T = L.
  Proof.
    intros. rewrite T_def2. rewrite phi0_def,delta_def.
    autounfold with R. autorewrite with R. field. auto.
  Qed.


(* ######################################################################### *)
(** * Model of Battery *)

(* ======================================================================= *)
(** ** Constants *)
Parameters
  C_b     (* 电池总容量 *)
  C_min   (* 电池最小总容量 *)
  K_b     (* 电池最大放电倍率 *)
  R_b     (* 电池内阻 *)
  I_b     (* 电池输出电流 *)
  U_b     (* 电池输出电压 *)
  T_b     (* 电池续航时间 *)
  : R.

(* ======================================================================= *)
(** ** Real numbers for compatibility with earlier than Coq 8.9 *)
Parameter val_0_06 : R.

(* ======================================================================= *)
(** ** Variables *)  

(* ======================================================================= *)
(** ** Predication for parameters checking *)
Definition is_C_b r := C_b = r.
Definition is_C_min r := C_min = r.
Definition is_K_b r := K_b = r.
Definition is_R_b r := R_b = r.
Definition is_I_b r := I_b = r.
Definition is_U_b r := U_b = r.
Definition is_T_b r := T_b = r.

(* ======================================================================= *)
(** ** Expand Auto DB *)
Global Hint Unfold
  is_C_b
  is_C_min
  is_K_b
  is_R_b
  is_I_b
  is_U_b
  is_T_b
  : fcs.

(* ======================================================================= *)
(** ** Assumptions *)
Axiom zero_le_I_b : 0 < I_b.
Axiom zero_le_U_b : 0 < U_b.

Global Hint Resolve 
  zero_le_I_b 
  zero_le_U_b
  : fcs.

(* ======================================================================= *)
(** ** Acceptted Theories *)

(** 4.22 *)
Axiom T_b_def : T_b = (C_b - C_min) / I_b * val_0_06.

(** 4.23 *)
Axiom I_b_limit : I_b <= (C_b * K_b) / 1000.



(* ######################################################################### *)
(** * Model of Motor *)

(* ======================================================================= *)
(** ** Constants *)
Parameters
  (* 常量 *)
  K_V0    (* 标称空载KV值，单位：rpm/V *)
  U_m0    (* 标称空载电压，单位：V *)
  I_m0    (* 标称空载电流，单位：A *)
  T_m0    (* 空载转矩，单位：N.m *)
  I_mMax  (* 最大电流，电流：A *)
  R_m     (* 电机内阻，单位：Ω *)
  G_m     (* 电机重量，单位：kg *)
  (* 变量 *)
  N_m0_MODEL    (* 空载转速，单位：rpm = r/min *)
  K_E_MODEL     (* 电机反电动势常数，单位：v/rpm *)
  K_T_MODEL     (* 电机转矩常数，单位：N.m *)
  U_m     (* 电机等效输入电压，单位：V *)
  I_m     (* 电机等效输入电流，也称电枢电流，单位：A *)
  E_a     (* 电机反电动势，单位：V *)
  T_e     (* 电机的电磁转矩，单位：N.m *)
  I_0_hat (* 实际空载电流，单位：A *)
  I_a     (* 转子驱动电流，单位：A *)
  : R.


(* ======================================================================= *)
(** ** Real numbers for compatibility with earlier than Coq 8.9 *)
Parameter val_9_55 : R.


(* ======================================================================= *)
(** ** Variables *)  

(* ======================================================================= *)
(** ** Predication for parameters checking *)
Definition is_K_V0 r := K_V0 = r.
Definition is_I_mMax r := I_mMax = r.
Definition is_I_m0 r := I_m0 = r.
Definition is_U_m0 r := U_m0 = r.
Definition is_R_m r := R_m = r.
Definition is_G_m r := G_m = r.
Definition is_U_m r := U_m = r.
Definition is_I_m r := I_m = r.
Definition is_E_a r := E_a = r.
Definition is_K_E r := K_E_MODEL = r.
Definition is_K_T r := K_T_MODEL = r.

(* ======================================================================= *)
(** ** Expand Auto DB *)
Global Hint Unfold
  is_K_V0
  is_I_mMax
  is_I_m0
  is_U_m0
  is_R_m
  is_G_m
  is_U_m
  is_I_m
  is_E_a
  is_K_E
  is_K_T
  : fcs.

(* ======================================================================= *)
(** ** Assumptions *)

Axiom zero_le_val_9_55 : 0 < val_9_55.
Axiom zero_le_K_E : 0 < K_E_MODEL.
Axiom zero_le_U_m0 : 0 < U_m0.
Axiom zero_le_K_V0 : 0 < K_V0.
Axiom zero_le_N_m0 : 0 < N_m0_MODEL.

Global Hint Resolve 
  zero_le_val_9_55
  zero_le_K_E
  zero_le_U_m0
  zero_le_K_V0
  zero_le_N_m0
  : fcs.


(* ======================================================================= *)
(** ** Acceptted Theories *)

(* --------------------------------------------------------------------- *)
(** *** p68, 电机等效模型 *)

(** 串联电路的电压关系 *)
Axiom motor_model_U : U_m = E_a + R_m * I_m.
(** 并联电路的电流关系 *)
Axiom motor_model_I : I_m = I_a + I_0_hat.


(* --------------------------------------------------------------------- *)
(** *** p80, 电机学模型 *)

(** 电机反电动势 *)
Axiom E_a_def : E_a = K_E_MODEL * N.

(** 电机电磁转矩 *)
Axiom T_e_def : T_e = K_T_MODEL * I_m.

(** 电机输出转矩，电磁转矩与空载转矩之差 *)
Axiom M_def3 : M = T_e - T_m0.

(** 电机输出转矩，等于螺旋桨转矩 *)
Axiom M_def4 : M = K_T_MODEL * I_a.

(** 电机空载转矩与实际空载电流成正比 *)
Axiom T_m0_def : T_m0 = K_T_MODEL * I_0_hat.

(** 标称空载情况下的关系式 *)
Axiom U_m0_def : U_m0 = K_E_MODEL * N_m0_MODEL + I_m0 * R_m.

(** p81，对于多旋翼电机，电机实际空载电流与标称空载电流差别不大 *)
Axiom I_0_hat_def : I_0_hat = I_m0.

(** 4.63，电机空载转速 *)
Axiom N_m0_def : N_m0_MODEL = K_V0 * U_m0.

(** 4.65，电机转矩常数与电机反电动势常数的关系 *)
Axiom K_T_and_K_E : K_T_MODEL = val_9_55 * K_E_MODEL.



(* ######################################################################### *)
(** * Model of ESC *)

(* ======================================================================= *)
(** ** Constants *)
Parameters
  I_eMax    (* 电调最大持续电流 *)
  R_e       (* 电调内阻 *)
  G_e       (* 电调重量 *)
  U_eo      (* 电调等效输出电压 *)
  U_e       (* 电调输入电压 *)
  I_e       (* 电调输入电流 *)
  sigma_e   (* 电调油门指令 *)
  I_other   (* 其他机载设备电流及损耗电流综合 *)
  : R.


(* ======================================================================= *)
(** ** Variables *)  


(* ======================================================================= *)
(** ** Predication for parameters checking *)
Definition is_I_eMax r := I_eMax = r.
Definition is_R_e r := R_e = r.
Definition is_G_e r := G_e = r.
Definition is_U_eo r := U_eo = r.
Definition is_U_e r := U_e = r.
Definition is_I_e r := I_e = r.
Definition is_sigma_e r := sigma_e = r.
Definition is_I_other r := I_other = r.
Definition is_N_m0 r := N_m0_MODEL = r.


(* ======================================================================= *)
(** ** Expand Auto DB *)
Global Hint Unfold
  is_I_eMax
  is_R_e
  is_G_e
  is_U_eo
  is_U_e
  is_I_e
  is_sigma_e
  is_I_other
  is_N_m0
  : fcs.


(* ======================================================================= *)
(** ** Assumptions *)


(* ======================================================================= *)
(** ** Acceptted Theories *)

(** 4.12 电调模型 *)
Axiom U_eo_def : U_eo = U_m + I_m * R_e.

(** 4.13 *)
Axiom sigma_e_def : sigma_e = U_eo / U_b.

(** 4.14 *)
Axiom I_e_def : I_e = sigma_e * I_m.

(** 4.15 *)
Axiom I_e_limit : I_e <= I_eMax.

(** 4.16 *)
Axiom U_e_def : U_e = U_b - I_b * R_b.

(** 4.17 *)
Axiom I_b_def : I_b = n_r * I_e + I_other.

Global
  Hint Rewrite
  U_eo_def sigma_e_def I_e_def U_e_def 
  : fcs.


(* ######################################################################### *)
(** * Model of Global/Other *)

(* ======================================================================= *)
(** ** Constants *)
Parameter theta_max : R.        (* 最大俯仰角，单位：rad *)
Parameter theta : R.            (* 俯仰角，单位：rad *)
Parameter State : PlaneState.   (* 飞行状态，枚举值，单位：无*)
Parameter G : R.                (* 多旋翼总重量，单位：N *)
Parameter G_maxload : R.        (* 多旋翼最大负载重量，单位：N *)
Parameter C_D1 : R.             (* 俯仰角在0°时的阻力系数 *)
Parameter C_D2 : R.             (* 俯仰角在90°时的阻力系数 *)
Parameter F_drag : R.           (* 作用在多旋翼上的阻力 *)
Parameter C_D : R.              (* 多旋翼整体的阻力系数，单位：无 *)
Parameter V : R.                (* 平飞速度，单位：m/s *)
Parameter S : R.                (* 飞行器最大截面面积，单位：m² *)


(* ======================================================================= *)
(** ** Variables *)
Parameter eta : R.              (* 系统效率 *)


(* ======================================================================= *)
(** ** Predication for parameters checking *)

Definition is_G_maxload r := G_maxload = r.
Definition is_theta_max r := theta_max = r.
Definition is_theta r := theta = r.
Definition is_State r := State = r.
Definition is_G r := G = r.
Definition is_V r := V = r.
Definition is_eta r := eta = r.


(* ======================================================================= *)
(** ** Expand Auto DB *)
Global Hint Unfold
  is_G_maxload
  is_theta_max
  is_theta
  is_State
  is_G
  is_V
  is_eta
  : fcs.


(* ======================================================================= *)
(** ** Assumptions *)

Axiom zero_le_G : 0 < G.
Axiom zero_le_S : 0 < S.

Global Hint Resolve
  zero_le_G
  zero_le_S
  : fcs.


(* ======================================================================= *)
(** ** Acceptted Theories *)

(** 悬停状态时的受力分析 *)
Axiom Hovering_Balance : State = Hovering -> G = T * n_r.

(** 最大负载模型 *)
Axiom G_maxload_def : G_maxload = T * n_r - G.

(** 最大俯仰角模型 *)
Axiom theta_max_def : theta_max = acos (G / (n_r * T)).

(** 4.37 平飞时的受力分析 *)
Axiom flatfly_hori : State = FlatFlying -> F_drag = G * tan theta.
Axiom flatfly_vert : State = FlatFlying -> T = G / (n_r * cos theta).

(** 4.38 平飞时的阻力公式 *)
Axiom F_drag_def : State = FlatFlying -> 
  F_drag = (1/2) * C_D * Rho * V * V * S.

(** 4.39 多旋翼整体的阻力系数，由CFD仿真数据拟合得到 *)
Axiom C_D_def : C_D = C_D1 * (1 - (sin theta)^3) + C_D2 * (1 - (cos theta)^3).

Theorem zero_le_C_D : 0 < C_D.
Proof.
  Admitted.

Global Hint Resolve
  zero_le_C_D : fcs.

(** 4.32 系统效率 *)
Axiom eta_def : eta =
  ((2 * PI) / 60) * n_r * M * N / (U_b * I_b).
