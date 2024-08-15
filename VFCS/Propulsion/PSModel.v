(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Model of Propulsion System, all theory from text book
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权

  remark    :
  1. we define val_0_0065 to repreents "0.0065", for several reasons
     * Earlier Coq version (such as 8.9 in 2021) don't support to typing decimal
     * better OCaml code extraction, because we will use float number "0.0065", 
       instead of constructed Q type (too complex and inefficient)
     * Constant value is irrelevance to the proof, we usually needn't to unfold it
  2. 模型层面，不需要处理时间问题。在具体应用中才要带上时间变量。
*)


Require Export RAux.

(* (** Generate a real number. eg: makeR 123 100 => 1.23 *) *)
(* Definition makeR : Z -> positive -> R := *)
(*   fun num den => Q2R (Qmake num den). *)

(* ######################################################################### *)
(** * Data structures *)

(** 飞行器状态 *)
Inductive PlaneState : Set :=
  | Hovering    (* 悬停中 *)
  | FlatFlying  (* 平飞，即拉力、俯仰角和重力满足一定关系 *)
  | Other       (* 其他 *)
  .


(* ######################################################################### *)
(** * Model of Environment *)

(* ======================================================================= *)
(** ** Constants *)
Parameter T0 : R.               (* 温度常数，= 273 K *)
Parameter P_a0 : R.             (* 标准大气压，= 101325 Pa *)
Parameter rho0 : R.             (* 标准大气密度，= 1.293 kg/m³ (0℃,273K) *)
Parameter h : R.                (* 海拔高度，单位：m *)
Parameter T_t : R.              (* 温度，单位：℃ *)
Parameter n_r : R.              (* 旋翼数目，单位：无 *)
Parameter val_0_0065 : R.       (* 计算压强时的一个系数 *)
Parameter val_5_2561 : R.       (* 计算压强时的一个系数 *)

(** ** Variables *)  
Parameter rho_MODEL : R.        (* 飞行环境空气密度，单位：kg/m³ *)
Parameter P_a_MODEL : R.        (* 大气压强，单位：Pa *)

(** ** Predication for parameters checking *)
Definition is_rho r := rho_MODEL = r.
Definition is_h r := h = r.
Definition is_rho0 r := rho0 = r.
Definition is_P_a r := P_a_MODEL = r.
Definition is_T_t r := T_t = r.
Definition is_n_r r := n_r = r.

(** ** Expand Auto DB *)
Global Hint Unfold
  is_rho
  is_h
  is_rho0
  is_P_a
  is_T_t
  is_n_r
  : fcs.

(** ** Assumptions *)

(** ** Acceptted Theories *)

(** 大气压强模型, 4.4 *)
Axiom P_a_def : P_a_MODEL = 
  P_a0 * (Rpower (1 - val_0_0065 * (h / (T0 + T_t))) val_5_2561).

(** 空气密度模型, 4.3 *)
Axiom rho_def : rho_MODEL = (T0 * P_a_MODEL) / (P_a0 * (T0 + T_t)) * rho0.


(* ######################################################################### *)
(** * Model of Propeler *)

(** ** Constants *)
Parameter D_p : R.           (* 螺旋桨直径，单位：m *)
Parameter H_p : R.           (* 螺旋桨螺距，单位：m *)
Parameter theta_p : R.       (* 桨叶角，单位：rad *)
Parameter epsilon : R.       (* 下洗效应带来的校正因子，单位: 无，要求为正实数 *)
Parameter phi0 : R.          (* 几何入流角，单位：rad *)
Parameter alpha : R.         (* 有效迎角，单位：rad *)
Parameter alpha0 : R.        (* 零升迎角，单位：rad *)
Parameter alpha_ab : R.      (* 绝对迎角，单位：rad *)
Parameter K0 : R.            (* ?，单位: 无 *)
Parameter c_p : R.           (* 平均几何弦长，单位：m *)
Parameter A : R.             (* 展弦比，单位: 无 *)
Parameter C1 : R.            (* 叶片截面翼型的升力系数，单位: 无 *)
Parameter C_fd : R.          (* 零升阻力系数，单位：无 *)
Parameter e : R.             (* Oswald因子，单位：无 *)
Parameter B_p : R.           (* 桨叶数，单位：无 *)
Parameter lambda : R.        (* 螺旋桨修正系数，单位：无 *)


(** ** Variables *)  
Parameter T : R.             (* 螺旋桨拉力，单位：N *)
Parameter M : R.             (* 螺旋桨扭矩，单位：N.m *)
Parameter N : R.             (* 螺旋桨转速，单位：r/min *)
Parameter propAngv : R.            (* 螺旋桨旋转角速度，单位：rad/s *)
Parameter C_d_MODEL : R.           (* 叶片截面翼型的阻力系数，单位：无 *)
Parameter C_T_MODEL : R.           (* 拉力系数, 单位：无 *)
Parameter C_M_MODEL : R.           (* 扭矩系数，单位：无 *)
Parameter S_sa : R.          (* 桨叶面积，单位：m² *)
Parameter W : R.             (* 桨叶上的来流速度，单位：m/s *)
Parameter L : R.             (* 叶片升力，单位：N *)
Parameter zeta : R.          (* zeta，单位：无 *)
Parameter gamma : R.         (* 下洗气流引起的阻升角，单位：rad *)
Parameter delta : R.         (* 下洗效应修正角，单位：rad*)
(* 拉力常数和扭矩常数，虽然依靠实验得到，但它的一个解析形式仍然值得验证 *)
Parameter c_T : R.           (* 简化的拉力常数, 单位：无，见6.1.3节 *)
Parameter c_M : R.           (* 简化的扭矩常数，单位：无，见6.1.3节 *)

(** ** Predication for parameters checking *)
Definition is_T r := T = r.
Definition is_M r := M = r.
Definition is_N r := N = r.
Definition is_propAngv r := propAngv = r.
Definition is_C_T r := C_T_MODEL = r.
Definition is_C_M r := C_M_MODEL = r.
Definition is_D_p r := D_p = r.
Definition is_H_p r := H_p = r.
Definition is_theta_p r := theta_p = r.
Definition is_epsilon r := epsilon = r.
Definition is_phi0 r := phi0 = r.
Definition is_alpha r := alpha = r.
Definition is_alpha0 r := alpha0 = r.
Definition is_alpha_ab r := alpha_ab = r.
Definition is_K0 r := K0 = r.
Definition is_c_p r := c_p = r.
Definition is_A r := A = r.
Definition is_C1 r := C1 = r.
Definition is_C_fd r := C_fd = r.
Definition is_e r := e = r.
Definition is_C_d r := C_d_MODEL = r.
Definition is_B_p r := B_p = r.
Definition is_lambda r := lambda = r.
Definition is_S_sa r := S_sa = r.
Definition is_W r := W = r.
Definition is_L r := L = r.
Definition is_zeta r := zeta = r.
Definition is_gamma r := gamma = r.
Definition is_delta r := delta = r.
Definition is_c_T r := c_T = r.
Definition is_c_M r := c_M = r.

(** ** Expand Auto DB *)
Global Hint Unfold
  is_T
  is_M
  is_N
  is_C_T
  is_C_M
  is_D_p
  is_H_p
  is_theta_p
  is_epsilon
  is_phi0
  is_alpha
  is_alpha0
  is_alpha_ab
  is_K0
  is_c_p
  is_A
  is_C1
  is_C_fd
  is_e
  is_C_d
  is_B_p
  is_lambda
  is_S_sa
  is_W
  is_L
  is_zeta
  is_gamma
  is_delta
  : fcs.

(** ** Assumptions *)
Axiom zero_le_n_r : 0 < n_r.
Axiom zero_le_D_p : 0 < D_p.
Axiom zero_le_c_p : 0 < c_p.
Axiom zero_le_K0 : 0 < K0.
Axiom zero_le_e : 0 < e.
Axiom zero_le_rho : 0 < rho_MODEL.
Axiom zero_le_lambda : 0 < lambda.
Axiom zero_le_zeta : 0 < zeta.
Axiom zero_le_B_p : 0 < B_p.
Axiom zero_le_alpha_ab : 0 < alpha_ab.
Axiom zero_le_A : 0 < A.
Axiom zero_le_C_fd : 0 < C_fd.
Axiom zero_le_epsilon : 0 < epsilon.
Axiom cos_gamma_neq0 : cos gamma <> 0.

Global Hint Resolve
  zero_le_n_r zero_le_D_p zero_le_c_p zero_le_K0 zero_le_e cos_gamma_neq0
  zero_le_rho zero_le_lambda zero_le_zeta zero_le_B_p zero_le_alpha_ab 
  zero_le_A zero_le_C_fd zero_le_epsilon
  : fcs.


(** ** Acceptted Theories *)

(** 6.16 螺旋桨旋转角速度(rad/s)与螺旋桨转速(rpm)的转换 *)
Axiom propAngv_by_N : propAngv = (N * 2 * PI) / 60.

Lemma N_by_propAngv : N = (propAngv * 60) / (2 * PI).
Proof. rewrite propAngv_by_N. ra. Qed.

(** 0 < N -> 0 < propAngv *)
Lemma N_gt0_imply_propAngv_gt0 : 0 < N -> 0 < propAngv.
Proof. intros. rewrite propAngv_by_N. gt0. Qed.

(** 0 < propAngv -> 0 < N *)
Lemma propAngv_gt0_imply_N_gt0 : 0 < propAngv -> 0 < N.
Proof. intros. rewrite N_by_propAngv. gt0. Qed.

(** 4.1 螺旋桨拉力计算模型 *)
Axiom T_def1 : T = C_T_MODEL * rho_MODEL * (N / 60)² * (D_p ^ 4).

(** 4.2 螺旋桨扭矩计算模型 *)
Axiom M_def1 : M = C_M_MODEL * rho_MODEL * (N / 60)² * (D_p ^ 5).

(** 4.47 桨叶角定义 *)
Axiom theta_p_def : theta_p = atan (H_p * / (PI * D_p)).

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
Axiom S_sa_def : S_sa = B_p * lambda * D_p * c_p / 2.

(** 4.51 叶片截面翼型的阻力系数定义 *)
Axiom C_d_def : C_d_MODEL = C_fd + (1 / (PI * A * e)) * (C1²).

(** 4.52 叶片升力定义 *)
Axiom L_def : L = (1/2) * C1 * rho_MODEL * S_sa * W².

(** 4.53 桨叶上的来流速度定义 *)
Axiom W_def : W = PI * zeta * D_p * (N / 60).

(** 4.54 由叶素理论建立的螺旋桨拉力模型 *)
Axiom T_def2 : T = L * (cos (gamma + phi0) / cos (gamma - delta)).

(** 4.55 螺旋桨扭矩的另一个模型 *)
Axiom M_def2 : M = (1/4) * rho_MODEL * B_p * C_d_MODEL * W² * S_sa * D_p.

(** p79 下洗气流引起的阻生角定义 *)
Axiom gamma_def : gamma = atan (C_d_MODEL / C1).

(** p79 下洗效应修正角可以忽略 *)
Axiom delta_def : delta = 0.

(** p112 简化的拉力系数的定义 *)
Axiom c_T_def : c_T = 1 / (4 * PI * PI) * rho_MODEL * (D_p ^ 4) * C_T_MODEL.

(** p112 简化的扭矩系数的定义 *)
Axiom c_M_def : c_M = 1 / (4 * PI * PI) * rho_MODEL * (D_p ^ 5) * C_M_MODEL.

Hint Rewrite
  theta_p_def phi0_def alpha_def alpha_ab_def
  A_def C1_def C_d_def S_sa_def L_def gamma_def delta_def W_def
  c_T_def c_M_def
  (* get_T_by_N T_def2 get_M_by_N M_def2 *)
  : fcs.


(** alpha的一个更常用的公式 *)
Lemma alpha_def2 : alpha = epsilon * atan (H_p * / (PI * D_p)).
Proof. autorewrite with fcs. unfold Rdiv. field. Qed.

(** T = L *)
Lemma T_by_L : cos gamma <> 0 -> T = L.
Proof.
  intros. rewrite T_def2. rewrite phi0_def,delta_def. ra.
Qed.


(* ######################################################################### *)
(** * Model of Battery *)

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

(** ** Real numbers for compatibility with earlier than Coq 8.9 *)
Parameter val_0_06 : R.

(** ** Variables *)  

(** ** Predication for parameters checking *)
Definition is_C_b r := C_b = r.
Definition is_C_min r := C_min = r.
Definition is_K_b r := K_b = r.
Definition is_R_b r := R_b = r.
Definition is_I_b r := I_b = r.
Definition is_U_b r := U_b = r.
Definition is_T_b r := T_b = r.

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

(** ** Assumptions *)
Axiom zero_le_I_b : 0 < I_b.
Axiom zero_le_U_b : 0 < U_b.

Global Hint Resolve 
  zero_le_I_b 
  zero_le_U_b
  : fcs.

(** ** Acceptted Theories *)

(** 4.22 电池放电模型 *)
Axiom T_b_def : T_b = (C_b - C_min) / I_b * val_0_06.

(** 4.23 电池放电电流限制模型 *)
Axiom I_b_limit : I_b <= (C_b * K_b) / 1000.


(* ######################################################################### *)
(** * Model of Motor *)

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

(** ** Real numbers for compatibility with earlier than Coq 8.9 *)
Parameter val_9_55 : R.

(** ** Variables *)  

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


(** ** Acceptted Theories *)

(** *** p68, 电机等效模型 *)

(** 电机等效模型之串联电路的电压关系 *)
Axiom motor_model_U : U_m = E_a + R_m * I_m.
(** 电机等效模型之并联电路的电流关系 *)
Axiom motor_model_I : I_m = I_a + I_0_hat.


(** *** p80, 电机学模型 *)

(** 电机反电动势 *)
Axiom E_a_def : E_a = K_E_MODEL * N.

(** 电机电磁转矩 *)
Axiom T_e_def : T_e = K_T_MODEL * I_m.

(** 电机输出转矩，等于电磁转矩与空载转矩之差 *)
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

(** ** Variables *)  

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

(** ** Assumptions *)

(** ** Acceptted Theories *)

(** 4.12 电调等效电路模型之电压关系 *)
Axiom U_eo_def : U_eo = U_m + I_m * R_e.

(** 4.13 电调油门指令与电压的关系 *)
Axiom sigma_e_def : sigma_e = U_eo / U_b.

(** 4.14 电调油门指令与电流的关系 *)
Axiom I_e_def : I_e = sigma_e * I_m.

(** 4.15 电调输入电流大小限制 *)
Axiom I_e_limit : I_e <= I_eMax.

(** 4.16 电调与电池的电压关系 *)
Axiom U_e_def : U_e = U_b - I_b * R_b.

(** 4.17 电调与电池的电流关系 *)
Axiom I_b_def : I_b = n_r * I_e + I_other.

Hint Rewrite
  U_eo_def sigma_e_def I_e_def U_e_def 
  : fcs.


(* ######################################################################### *)
(** * Model of Global/Other *)

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

(** ** Variables *)
Parameter eta : R.              (* 系统效率 *)

(** ** Predication for parameters checking *)

Definition is_G_maxload r := G_maxload = r.
Definition is_theta_max r := theta_max = r.
Definition is_theta r := theta = r.
Definition is_State r := State = r.
Definition is_G r := G = r.
Definition is_V r := V = r.
Definition is_eta r := eta = r.

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

(** ** Assumptions *)

Axiom zero_le_G : 0 < G.
Axiom zero_le_S : 0 < S.

Global Hint Resolve
  zero_le_G
  zero_le_S
  : fcs.


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
  F_drag = (1/2) * C_D * rho_MODEL * V * V * S.

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
