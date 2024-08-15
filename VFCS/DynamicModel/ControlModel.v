(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Multicopter Control Model 多旋翼控制模型
  author    : Zhengpu Shi
  date      : Nov, 2023

  reference : 
  1. Introduction to Multicopter Design and Control, QuanQuan, 2017

  remark    :
  1. 螺旋桨产生的反扭力矩，也称旋转力矩，简称力矩
     力矩方向一般假设为平行于飞机所在平面，垂直于机臂
     物体受力后旋转的物理量，τ = F × d
 *)

Require Export PS.
Require Export AttitudeRepr.

Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * 多旋翼飞行控制刚体模型 *)

(* 对多旋翼建模时，做了一些简化的假设，见 Config.v 中的说明 *)

(* ======================================================================= *)
(** ** 刚体运动学模型 *)
Section RigidKinematicsModel.

  (** 多旋翼的重心向量(与时间相关的函数) *)
  Variable e_p : R -> vec 3.

  (** 多旋翼的速度向量 *)
  Variable e_v : R -> vec 3.

  (** 速度与位置的模型 *)
  Axiom positionVelocityMODEL : vderiv e_p = e_v.

  (** 机体旋转角速度，可由传感器测量得到 *)
  Variable b_angvx b_angvy b_angvz : R -> R.
  Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
  Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
  Notation b_ω := b_angv.

  (** *** 欧拉角模型 *)
  Section eulerMODEL.

    (** 假设欧拉角（姿态角）*)
    Variable roll : R -> R.      (* 绕 x 轴旋转的滚转角 *)
    Variable pitch : R -> R.     (* 绕 y 轴旋转的俯仰角 *)
    Variable yaw : R -> R.       (* 绕 z 轴旋转的偏航角 *)
    Notation ϕ := roll. Notation θ := pitch. Notation ψ := yaw.
    Let Φ : R -> vec 3 := fun t => l2v [ϕ t; θ t; ψ t].
    
    (** 从机体旋转角速度到欧拉角变化率（导数）的转换矩阵 *)
    Let W (t : R) : smat 3 :=
          let s1 := sin (ϕ t) in
          let c1 := cos (ϕ t) in
          let s2 := sin (θ t) in
          let c2 := cos (θ t) in
          let t2 := tan (θ t) in
          l2m [[1; t2 * s1; t2 * c1];
               [0; c1; - s1];
               [0; s1 / c2; c1 / c2]]%R.

    (** 欧拉角模型，即欧拉角变化率与机体旋转角速度的关系 *)
    Lemma eulerMODEL :
      (forall t, pitchValid (θ t)) ->
      vderiv Φ = fun t => W t *v b_ω t.
    Proof.
      intros.
      pose proof (angv2eulerRateMAT_spec ϕ θ ψ b_ωx b_ωy b_ωz). extensionality t.
      replace (vderiv Φ) with (fun t0 : R => @l2v 3 [(ϕ ') t0; (θ ') t0; (ψ ') t0]).
      - apply (H0 t). auto.
      - unfold vderiv. extensionality t0. veq.
    Qed.
  End eulerMODEL.

  (** *** 旋转矩阵模型 *)
  Section matrixMODEL.

    (** 给定旋转矩阵 *)
    Variable Rb2e : R -> mat 3 3.

    (** 旋转矩阵模型，即旋转矩阵变化率与机体旋转角速度的关系 *)
    Lemma matrixMODEL :
      (forall t, SOnP (Rb2e t)) ->
      mderiv Rb2e = fun t => Rb2e t * skew3 (b_ω t).
    Proof. intros. apply derivRb2e_eq; auto. Qed.
  End matrixMODEL.

  (** *** 四元数模型 *)
  Section quatMODEL.
    (** 假设 {e}相对于{b} 的四元数 *)
    Variable q_e2b : R -> quat.
    Let q0 := fun t => (q_e2b t).W.
    Let qv := fun t => (q_e2b t).Im.

    (** 四元数W分量q0的模型，即q0的导数与机体角速度b_ω的关系 *)
    Lemma quatMODEL_W :
      (forall t : R, b_ω t <> vzero) ->
      (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
      q0 ' = fun t => <(-(1/2))%R s* qv t, b_ω t>.
    Proof. intros. apply derivQuat_W_eq; auto. Qed.

    (** 四元数Im分量qv的模型，即qv的导数与机体角速度b_ω的关系 *)
    Lemma quatMODEL_Im :
      (forall t : R, b_ω t <> vzero) ->
      (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
      vderiv qv = fun t => (((1/2) s* (q0 t s* mat1 + skew3 (qv t))) *v (b_ω t))%M.
    Proof. intros. apply derivQuat_Im_eq; auto. Qed.
  End quatMODEL.
End RigidKinematicsModel.


(* ======================================================================= *)
(** ** 多旋翼刚体动力学模型 *)

Section RigidDynamicsModel.

  (** 假设机体旋转角速度如下 *)
  Variable b_angvx b_angvy b_angvz : R -> R.
  Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
  Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
  Notation b_ω := b_angv.

  (** *** 位置动力学模型，即速度的导数、姿态角、拉力之间的关系 *)
  Section Position.

    (** 假设 {b} 相对于 {e} 的旋转矩阵为 *)
    Variable Rb2e : R -> smat 3.
    Hypotheses H_Rb2e_SO3 : forall t, SOnP (Rb2e t).

    (** 机体 z 轴的矢量在 {b} 中的表示为 *)
    Let b_b3 : R -> vec 3 := fun t => v3j.
    (** 于是，机体 z 轴的矢量在 {e} 中的表示为 *)
    Let e_b3 : R -> vec 3 := fun t => (Rb2e t) *v (b_b3 t).

    (** 假设螺旋桨总拉力 *)
    Variable f : R -> R.
    Axiom f_ge0 : forall t, 0 <= f t. (* 拉力非负 *)

    (** 假设速度矢量 v 在 {e} *)
    Variable e_v : R -> vec 3.

    (** 受力模型：有两个力，沿e_z轴正向的重力，沿b_z轴负向的拉力。由牛顿第二定理得 *)
    Axiom forceMODEL : forall (t : R),
        Config.m s* (vderiv e_v t) =
          (Config.m * Config.g)%R s* v3j + (- f t)%R s* e_b3 t.

    (** 在{e}下的位置动力学模型 *)
    Lemma positionMODEL_E :
      vderiv e_v =
        fun t => Config.g s* v3j + ((- f t) / Config.m)%R s* e_b3 t.
    Proof.
      extensionality t. pose proof (forceMODEL t).
      apply vscal_eq_reg_l with (x := Config.m); auto with fcs.
      rewrite H. rewrite vscal_vadd. rewrite !vscal_assoc. f_equal. f_equal.
      autounfold with tA. field. auto with fcs.
    Qed.

    (** 在{b}下的位置动力学模型 *)
    Section positionMODEL_in_body_frame.

      (** 假设速度矢量 v 在 {b} 中的坐标如下，它与 e_v 具有转换关系 *)
      Variable b_v : R -> vec 3.
      Axiom H_ev_bv : forall t, e_v t = Rb2e t *v b_v t.

      (** b_v的导数的等价形式 \dot{e_v} = R * \dot{b_v} + R * skew3(b_ω) * b_v *)
      Fact deriv_ev_eq1 :
        vderiv e_v =
          fun t => Rb2e t *v (vderiv b_v t) + (Rb2e t * skew3 (b_ω t))%M *v b_v t.
      Proof.
        assert (vderiv e_v = vderiv (fun t => Rb2e t *v b_v t)).
        { f_equal. extensionality t. apply H_ev_bv. }
        rewrite H. rewrite vderiv_mmulv. extensionality t. f_equal.
        rewrite (matrixMODEL b_ωx b_ωy b_ωz Rb2e); auto.
      Qed.

      Lemma positionMODEL_B :
        vderiv b_v =
          fun t => - (skew3 (b_ω t) *v b_v t) +
                   Config.g s* (Rb2e t)\T *v v3j +
                   ((- f t) / Config.m)%R s* v3j.
      Proof.
        pose proof (deriv_ev_eq1).
        pose proof (positionMODEL_E). rewrite H in H0.
        extensionality t.
        replace (vderiv e_v) with (vderiv (fun t => Rb2e t *v b_v t)).
        2:{ f_equal. extensionality t0. rewrite H_ev_bv. auto. }
        rewrite fun_eq_iff_forall_eq in H0. specialize (H0 t).
        apply (fun_app (mmulv (Rb2e t\T))) in H0.
        rewrite !mmulv_vadd in H0.
        rewrite <- !mmulv_assoc in H0. rewrite <- !mmul_assoc in H0.
        destruct (H_Rb2e_SO3 t). rewrite morth_iff_mul_trans_l in H1.
        rewrite H1 in H0. rewrite mmulv_1_l in H0. rewrite mmul_1_l in H0.
        rewrite vadd_assoc.
        (* Tips：使用代数结构中开发的策略 agroup 来自动化 *)
        match goal with | |- ?a = - ?b + ?c => assert (a + b = c) end.
        2:{ rewrite <- H3. pose proof (vadd_AGroup 3). agroup. }
        rewrite H0. rewrite !mmulv_vscal. f_equal. f_equal.
        unfold e_b3. rewrite <- mmulv_assoc. rewrite H1. rewrite mmulv_1_l. auto.
      Qed.

    End positionMODEL_in_body_frame.

  End Position.

  (** *** 姿态动力学模型 *)
  Section Pose.

    (** 假设螺旋桨在机体轴上产生的力矩(propeller torque) 在{b}下的表示如下 *)
    Variable b_torqPx b_torqPy b_torqPz : R -> R.
    Notation b_τx := b_torqPx. Notation b_τy := b_torqPy. Notation b_τz := b_torqPz.
    Let b_torqP (t : R) : vec 3 := l2v [b_τx t; b_τy t; b_τz t].
    Notation b_τ := b_torqP.

    (** 假设第i个螺旋桨在t时刻的角速度 (rad/s) *)
    Variable propAngv : nat -> R -> R.
    Notation ϖ := propAngv.

    (** 机体z轴在{b}中的表示 *)
    Let b_b3 : R -> vec 3 := fun t => v3k.

    (** 第i个螺旋桨产生的陀螺力矩(gyroscopic torques)，其符号与螺旋桨的旋转方向有关 *)
    Definition gyroTorqueOne (i : nat) (t : R) : vec 3 :=
      (Config.JRP * rotDir2val i * propAngv i t)%R s* (b_b3 t \x b_ω t).

    (** 单个螺旋桨的陀螺力矩的等价形式。包括：展开 b_b3，并交换叉乘顺序等 *)
    Lemma gyroTorqueOne_eq : forall (i : nat) (t : R),
        gyroTorqueOne i t =
          (Config.JRP * propAngv i t * rotDir2val (S i))%R s* (b_ω t \x v3k).
    Proof.
      intros. unfold gyroTorqueOne. rewrite v3cross_anticomm.
      rewrite vscal_vopp. rewrite <- vscal_opp. unfold b_b3. f_equal.
      pose proof (Radd_AGroup). rewrite rotDir2val_S.
      autounfold with tA. lra.
    Qed.

    (** 机体旋转角速度与 v3k叉乘后的向量只会在 x,y 平面内 *)
    Fact angv_cross_v3k_eq : forall t, b_ω t \x v3k = l2v [b_ωy t; - b_ωx t; 0]%R.
    Proof. intros. clear. veq; ra. Qed.

    (** 所有的旋翼陀螺力矩 *)
    Definition gyroTorque (t : R) (n : nat) : vec 3 :=
      @seqsum _ vadd vzero n (fun i => gyroTorqueOne i t).

    (** 当前配置下的所有的旋翼陀螺力矩 *)
    Let Gall : R -> vec 3 := fun t => gyroTorque t Config.rotorCountNat.

    (* 进一步分析，可以得到三个方向上的陀螺力矩分量 *)

    (** 在 xb 方向的陀螺力矩 *)
    Lemma gyroTorque_x : forall t n,
        (gyroTorque t n).1 =
          @seqsum _ Rplus 0 n
            (fun i => Config.JRP * b_ωy t * rotDir2val (S i) * ϖ i t)%R.
    Proof.
      intros. unfold gyroTorque. rewrite vnth_seqsum_vadd.
      f_equal. extensionality i.
      rewrite gyroTorqueOne_eq. rewrite angv_cross_v3k_eq.
      rewrite vnth_vscal. rewrite vnth_l2v. simpl.
      autounfold with tA. ring.
    Qed.

    (** 在 yb 方向的陀螺力矩 *)
    Lemma gyroTorque_y : forall t n,
        (gyroTorque t n).2 =
          @seqsum _ Rplus 0 n (fun i => Config.JRP * b_ωx t * rotDir2val i * ϖ i t)%R.
    Proof.
      intros. unfold gyroTorque.
      rewrite vnth_seqsum_vadd. f_equal. extensionality i.
      rewrite gyroTorqueOne_eq. rewrite angv_cross_v3k_eq.
      rewrite vnth_vscal. rewrite vnth_l2v. simpl.
      rewrite rotDir2val_S. autounfold with tA. ring.
    Qed.

    (** 在 yz 方向的陀螺力矩 *)
    Lemma gyroTorque_z : forall t n, (gyroTorque t n).3 = 0.
    Proof.
      intros. unfold gyroTorque. rewrite vnth_seqsum_vadd.
      apply seqsum_eq0. intros. rewrite gyroTorqueOne_eq.
      rewrite angv_cross_v3k_eq. rewrite vnth_vscal. rewrite vnth_l2v. simpl.
      autounfold with tA. ring.
    Qed.

    (** 在机体坐标系{b}中建立姿态动力学方程 *)
    Axiom attitudeMODEL_B : forall t,
        Config.J *v (vderiv b_ω t) =
          - (b_ω t \x (Config.J *v b_ω t)) + Gall t + b_τ t.

  End Pose.
    
End RigidDynamicsModel.


(* ======================================================================= *)
(** ** 多旋翼飞行控制刚体模型，由刚体运动学模型和刚体动力学模型联立后得到 *)

(** *** 欧拉角表示下的模型 *)
Module EulerRigidModel.

  Section euler.

    (** 多旋翼的重心向量(与时间相关的函数) *)
    Variable e_p : R -> vec 3.

    (** 多旋翼的速度向量 *)
    Variable e_v : R -> vec 3.
    
    (** 机体旋转角速度，可由传感器测量得到 *)
    Variable b_angvx b_angvy b_angvz : R -> R.
    Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
    Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
    Notation b_ω := b_angv.

    (** 假设螺旋桨总拉力 *)
    Variable f : R -> R.
    Hypotheses f_ge0 : forall t, 0 <= f t. (* 拉力非负 *)

    (** 假设第i个螺旋桨在t时刻的角速度 (rad/s) *)
    Variable propAngv : nat -> R -> R.
    Notation ϖ := propAngv.

    (** 假设螺旋桨在机体轴上产生的力矩(propeller torque) 在{b}下的表示如下 *)
    Variable b_torqPx b_torqPy b_torqPz : R -> R.
    Notation b_τx := b_torqPx. Notation b_τy := b_torqPy. Notation b_τz := b_torqPz.
    Let b_torqP (t : R) : vec 3 := l2v [b_τx t; b_τy t; b_τz t].
    Notation b_τ := b_torqP.

    (** 假设欧拉角（姿态角）*)
    Variable roll : R -> R.      (* 绕 x 轴旋转的滚转角 *)
    Variable pitch : R -> R.     (* 绕 y 轴旋转的俯仰角 *)
    Variable yaw : R -> R.       (* 绕 z 轴旋转的偏航角 *)
    Notation ϕ := roll. Notation θ := pitch. Notation ψ := yaw.
    Let Φ : R -> vec 3 := fun t => l2v [ϕ t; θ t; ψ t].

    (** 机体坐标系 {b} 相对于 {e} 的位姿（转换矩阵） *)
    Definition Rb2e (t : R) : smat 3 := b2eMAT (ϕ t) (θ t) (ψ t).

    (** 从机体旋转角速度到欧拉角变化率（导数）的转换矩阵 *)
    Definition W (t : R) : smat 3 := angv2eulerRateMAT (ϕ t) (θ t).

    (** 当前配置下的所有的旋翼陀螺力矩 *)
    Definition gyroTorqueAll : R -> vec 3 :=
      fun t => gyroTorque b_ωx b_ωy b_ωz propAngv t Config.rotorCountNat.

    (** {e}中的位置矢量和速度矢量之间的关系 *)
    Theorem position_and_velocity : vderiv e_p = e_v.
    Proof. apply positionVelocityMODEL. Qed.

    (** {e}中的速度矢量、螺旋桨总拉力、欧拉角之间的关系。注意，这里使用了旋转矩阵 *)
    Theorem velocity_and_force_euler :
      vderiv e_v =
        fun t => Config.g s* v3j + ((- f t) / Config.m)%R s* (Rb2e t *v v3j).
    Proof. apply (positionMODEL_E Rb2e f). Qed.

    (** {b}中的机体角速度、陀螺力矩和螺旋桨在机体轴上的力矩之间的关系 *)
    Theorem angV_gyroTorque_propTorque : forall t,
        Config.J *v (vderiv b_ω t) =
          - (b_ω t \x (Config.J *v b_ω t)) + gyroTorqueAll t + b_τ t.
    Proof. intros. apply attitudeMODEL_B. Qed.

    (** 欧拉角和{b}中的机体角速度之间的关系 *)
    Theorem eulerAng_and_angV :
      (forall t, pitchValid (θ t)) -> vderiv Φ = fun t => W t *v b_ω t.
    Proof. intros. apply eulerMODEL; auto. Qed.
  End euler.
End EulerRigidModel.

(** *** 旋转矩阵表示下的模型 *)
Module MatrixRigidModel.

  Section matrix.

    (** 多旋翼的重心向量(与时间相关的函数) *)
    Variable e_p : R -> vec 3.

    (** 多旋翼的速度向量 *)
    Variable e_v : R -> vec 3.

    (** 机体旋转角速度，可由传感器测量得到 *)
    Variable b_angvx b_angvy b_angvz : R -> R.
    Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
    Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
    Notation b_ω := b_angv.

    (** 假设螺旋桨总拉力 *)
    Variable f : R -> R.
    Hypotheses f_ge0 : forall t, 0 <= f t. (* 拉力非负 *)

    (** 假设第i个螺旋桨在t时刻的角速度 (rad/s) *)
    Variable propAngv : nat -> R -> R.
    Notation ϖ := propAngv.

    (** 假设螺旋桨在机体轴上产生的力矩(propeller torque) 在{b}下的表示如下 *)
    Variable b_torqPx b_torqPy b_torqPz : R -> R.
    Notation b_τx := b_torqPx. Notation b_τy := b_torqPy. Notation b_τz := b_torqPz.
    Let b_torqP (t : R) : vec 3 := l2v [b_τx t; b_τy t; b_τz t].
    Notation b_τ := b_torqP.

    (** 设{b}相对于{e}的旋转矩阵为 *)
    Variable Rb2e : R -> smat 3.
    (** 旋转矩阵还要满足 SO(3) 的性质 *)
    Hypotheses Rb2e_SO3 : forall t, SOnP (Rb2e t).

    (** 当前配置下的所有的旋翼陀螺力矩 *)
    Definition gyroTorqueAll : R -> vec 3 :=
      fun t => gyroTorque b_ωx b_ωy b_ωz propAngv t Config.rotorCountNat.

    (** {e}中的位置矢量和速度矢量之间的关系 *)
    Theorem position_and_velocity : vderiv e_p = e_v.
    Proof. apply positionVelocityMODEL. Qed.

    (** {e}中的速度矢量、螺旋桨总拉力、欧拉角之间的关系。注意，这里使用了旋转矩阵 *)
    Theorem velocity_and_force_euler :
      vderiv e_v =
        fun t => Config.g s* v3j + ((- f t) / Config.m)%R s* (Rb2e t *v v3j).
    Proof. apply (positionMODEL_E Rb2e f). Qed.

    (** {b}中的机体角速度、陀螺力矩和螺旋桨在机体轴上的力矩之间的关系 *)
    Theorem angV_gyroTorque_propTorque : forall t,
        Config.J *v (vderiv b_ω t) =
          - (b_ω t \x (Config.J *v b_ω t)) + gyroTorqueAll t + b_τ t.
    Proof. intros. apply attitudeMODEL_B. Qed.

    (** 旋转矩阵和{b}中的机体角速度之间的关系 *)
    Theorem eulerAng_and_angV :
      mderiv Rb2e = fun t => Rb2e t * skew3 (b_ω t).
    Proof. apply (derivRb2e_eq). auto. Qed.
  End matrix.
End MatrixRigidModel.

(** *** 四元数表示下的模型 *)
Module QuatRigidModel.

  Section quat.

    (** 多旋翼的重心向量(与时间相关的函数) *)
    Variable e_p : R -> vec 3.

    (** 多旋翼的速度向量 *)
    Variable e_v : R -> vec 3.

    (** 机体旋转角速度，可由传感器测量得到 *)
    Variable b_angvx b_angvy b_angvz : R -> R.
    Notation b_ωx := b_angvx. Notation b_ωy := b_angvy. Notation b_ωz := b_angvz.
    Let b_angv (t : R) : vec 3 := l2v [b_ωx t; b_ωy t; b_ωz t].
    Notation b_ω := b_angv.

    (** 假设螺旋桨总拉力 *)
    Variable f : R -> R.
    Hypotheses f_ge0 : forall t, 0 <= f t. (* 拉力非负 *)

    (** 假设第i个螺旋桨在t时刻的角速度 (rad/s) *)
    Variable propAngv : nat -> R -> R.
    Notation ϖ := propAngv.

    (** 假设螺旋桨在机体轴上产生的力矩(propeller torque) 在{b}下的表示如下 *)
    Variable b_torqPx b_torqPy b_torqPz : R -> R.
    Notation b_τx := b_torqPx. Notation b_τy := b_torqPy. Notation b_τz := b_torqPz.
    Let b_torqP (t : R) : vec 3 := l2v [b_τx t; b_τy t; b_τz t].
    Notation b_τ := b_torqP.

    (** 设 {e} 相对于 {b} 的四元数如下。注意，不是 {b} 相对于 {e} *)
    Variable q_e2b : R -> quat.

    (** ToDo: 这两个额外的假设，暂时没有给出更详细的研究 *)
    Hypotheses H_b_angv_neq0 : forall t, b_ω t <> vzero.
    Hypotheses H_b_angv_is_small : forall t h : R, is_small ((||b_ω t||) * h / 2).

    (** 四元数的W分量 *)
    Definition quatW : R -> R := fun t => (q_e2b t).W.

    (** 四元数的Im分量 *)
    Definition quatIm : R -> vec 3 := fun t => (q_e2b t).Im.

    (** 机体坐标系 {b} 相对于 {e} 的位姿（转换矩阵） *)
    Definition Rb2e (t : R) : smat 3 := q2m (q_e2b t).

    (** 当前配置下的所有的旋翼陀螺力矩 *)
    Definition gyroTorqueAll : R -> vec 3 :=
      fun t => gyroTorque b_ωx b_ωy b_ωz propAngv t Config.rotorCountNat.

    (** {e}中的位置矢量和速度矢量之间的关系 *)
    Theorem position_and_velocity : vderiv e_p = e_v.
    Proof. apply positionVelocityMODEL. Qed.

    (** {e}中的速度矢量、螺旋桨总拉力、欧拉角之间的关系。注意，这里使用了旋转矩阵 *)
    Theorem velocity_and_force_euler :
      vderiv e_v =
        fun t => Config.g s* v3j + ((- f t) / Config.m)%R s* (Rb2e t *v v3j).
    Proof. apply (positionMODEL_E Rb2e f). Qed.

    (** {b}中的机体角速度、陀螺力矩和螺旋桨在机体轴上的力矩之间的关系 *)
    Theorem angV_gyroTorque_propTorque : forall t,
        Config.J *v (vderiv b_ω t) =
          - (b_ω t \x (Config.J *v b_ω t)) + gyroTorqueAll t + b_τ t.
    Proof. intros. apply attitudeMODEL_B. Qed.

    (** 四元数W分量变化率与{b}中机体角速度的关系 *)
    Theorem quatW_and_angV :
      quatW ' = fun t => <((-(1/2))%R s* quatIm t)%V, b_ω t>.
    Proof. apply derivQuat_W_eq; auto. Qed.

    (** 四元数Im分量变化率与{b}中机体角速度的关系 *)
    Theorem quatIm_and_angV :
      vderiv quatIm = fun t => ((1/2) s* (quatW t s* mat1 + skew3 (quatIm t)))%M *v (b_ω t).
    Proof. apply derivQuat_Im_eq; auto. Qed.
  End quat.
End QuatRigidModel.


(* ######################################################################### *)
(** * 控制效率模型 *)

(* ======================================================================= *)
(** ** 单个螺旋桨的拉力和反扭力矩模型 *)
(* 拉力和反扭矩的原理：
   参考：
   https://www.askpure.com/course_7SR7K4NZ-V5DGOW2H-Q5OXGY5H-JJB712HG.html
   https://www.wrjzx.com/214i4.html

   1. 多旋翼的动力系来源于高速电机带动螺旋桨转动而产生的拉力。
   2. 假设电机带动螺旋桨顺时针运动，由于桨叶螺距对空气作用的效果会产生一个向下的推力与
      水平方向的推力。（无论叶片怎么摆放，或旋转方向如何，推力总是z轴负方向）
   3. 向下的推力是桨对空气的作用力，根据反作用力原理，空气就会对桨产生一个向上的推力。
      这就是空气对桨进而作用到机身垂直方向的拉力。
   4. 而水平方向对空气的推力同样会产生一个空气对桨的反作用力，方向与作用力相反，其
      作用到多旋翼的轴臂上，就产生了我们所说的反扭力，也称反扭力矩。

   总结：
   1. 拉力：由于螺旋桨旋转带动空气并反作用于机身的拉力，永远垂直于zb轴负方向。
      记作 T
   2. 反扭力矩：由于螺旋桨旋转带动空气并反作用于机身的反转力矩。
      记作 M
 *)
Section onePropellerControlModel.
  (** 假设单个螺旋桨在t时刻的旋转角速度(rad/s) *)
  Variable propAngv : R -> R.
  Notation ϖ := propAngv.

  (** *** 螺旋桨拉力的模型 *)

  (** 单个螺旋桨在t时刻产生的拉力(N) *)
  Definition onePropThrust (t : R) : R := (Config.c_T * (ϖ t * ϖ t))%R.
  Notation T := onePropThrust.

  (** 验证此处的定义与PS中的理论一致 *)
  Lemma onePropThrust_spec : forall t, T t = PSTheory.get_T_by_propAngv (ϖ t).
  Proof. intros. auto. Qed.

  (** 螺旋桨反扭矩模型有两个：
     1. 静态模型：多旋翼在无风情况下悬停时
     2. 动态模型：包括了动态分量 *)

  (** 静态模型：单个螺旋桨在t时刻产生的反扭力矩(N.m) *)
  Definition onePropTorque (t : R) : R := (Config.c_M * (ϖ t * ϖ t))%R.
  Notation M := onePropTorque.

  (** 验证此处的定义与PS中的理论一致 *)
  Lemma onePropTorque_spec : forall t, M t = PSTheory.get_M_by_propAngv (ϖ t).
  Proof. intros. auto. Qed.

  (** 动态模型：单个螺旋桨在t时刻产生的反扭力矩(N.m) *)
  Definition onePropTorqueDynamic (t : R) : R :=
    (Config.c_M * (ϖ t * ϖ t) + Config.JRP * (ϖ ' t))%R.

  (* ToDo: 上述定义来自公式 6.19，没有做进一步研究 *)
    
End onePropellerControlModel.


(* ======================================================================= *)
(** ** 拉力和力矩模型（整体，而非单个螺旋桨） *)

(** *** 十字形四旋翼的拉力力矩模型 *)
Module PQuadThrustTorque.
  Open Scope R_scope.
  Section thrust_torque.
    (** 无人机全局固有参数的缩写，为了简化输入 *)
    Let c_T := Config.c_T.
    Let c_M := Config.c_M.
    Let d := Config.d.

    (** 各螺旋桨的转速 (rad/s) *)
    Variable propAngv : R -> vec 4.
    Notation ϖ1 := (fun t => (propAngv t).1).
    Notation ϖ2 := (fun t => (propAngv t).2).
    Notation ϖ3 := (fun t => (propAngv t).3).
    Notation ϖ4 := (fun t => (propAngv t).4).

    (** 作用在该旋翼上的总拉力 *)
    Definition thrust (t : R) : R :=
      c_T * ((ϖ1 t)² + (ϖ2 t)² + (ϖ3 t)² + (ϖ4 t)²).

    (** f = ∑T_i *)
    Lemma thrust_spec : forall t,
        thrust t = vsum (fun i => onePropThrust (fun x => propAngv x i) t).
    Proof. intros. unfold thrust, onePropThrust. v2e (propAngv t). cbv. ra. Qed.

    (* 各个桨的旋转对机体力矩的贡献
       桨1,3逆时针转，产生顺时针的反作用力，使飞行器顺时针转；
       桨2,4顺时针转，产生逆时针的反作用力，使飞行器逆时针转；
       桨1的升力使x轴反转，力臂为d，力矩使z轴正转
       桨2的升力使y轴正转，力臂为d，力矩使z轴反转
       桨4的升力使y轴反转，力臂为d，力矩使z轴正转
       桨4的升力使x轴正转，力臂为d，力矩使z轴反转 *)

    (** 螺旋桨在xb轴上产生的滚转力矩 *)
    Definition torquex (t : R) := d * c_T * (- (ϖ2 t)² + (ϖ4 t)²).
    (** 螺旋桨在yb轴上产生的俯仰力矩 *)
    Definition torquey (t : R) := d * c_T * ((ϖ1 t)² - (ϖ3 t)²).
    (** 螺旋桨在zb轴上产生的偏航力矩 *)
    Definition torquez (t : R) :=
      c_M * ((ϖ1 t)² - (ϖ2 t)² + (ϖ3 t)² - (ϖ4 t)²).
    Notation τx := torquex.
    Notation τy := torquey.
    Notation τz := torquez.

    (* 合并拉力和力矩，构造统一的控制效率模型矩阵 *)

    (** 拉力和力矩构成的向量 [f;τx;τy;τz] *)
    Definition thrustTorque (t : R) : vec 4 := l2v [thrust t; τx t; τy t; τz t].
    (** 螺旋桨旋转角速度平方的向量 [ϖ1²;ϖ2²;ϖ3²;ϖ4²] *)
    Definition propAngvSquare (t : R) : vec 4 :=
      l2v [(ϖ1 t)²; (ϖ2 t)²; (ϖ3 t)²; (ϖ4 t)²].
    (** 由螺旋桨旋转角速度计算拉力和力矩的控制效率矩阵  *)
    Definition controlMat : smat 4 :=
      l2m [[c_T; c_T; c_T; c_T];
           [0; - d * c_T; 0; d * c_T];
           [d * c_T; 0; - d * c_T; 0];
           [c_M; - c_M; c_M; - c_M]].

    (** 控制效率模型 *)
    Lemma thrustTorque_eq : forall t, thrustTorque t = controlMat *v propAngvSquare t.
    Proof.
      intros. unfold thrustTorque, controlMat, propAngvSquare.
      unfold thrust, torquex, torquey, torquez. v2e (propAngv t). veq; try lra.
    Qed.
  End thrust_torque.
End PQuadThrustTorque.

(** *** X字形四旋翼的拉力力矩模型 *)
Module XQuadThrustTorque.
  Open Scope R_scope.
  Section thrust_torque.
    (** 无人机全局固有参数的缩写，为了简化输入 *)
    Let c_T := Config.c_T.
    Let c_M := Config.c_M.
    Let d := Config.d.

    (** 各螺旋桨的转速 (rad/s) *)
    Variable propAngv : R -> vec 4.
    Notation ϖ1 := (fun t => (propAngv t).1).
    Notation ϖ2 := (fun t => (propAngv t).2).
    Notation ϖ3 := (fun t => (propAngv t).3).
    Notation ϖ4 := (fun t => (propAngv t).4).

    (** 作用在该旋翼上的总拉力 *)
    Definition thrust (t : R) : R :=
      c_T * ((ϖ1 t)² + (ϖ2 t)² + (ϖ3 t)² + (ϖ4 t)²).

    (** f = ∑T_i *)
    Lemma thrust_spec : forall t,
        thrust t = vsum (fun i => onePropThrust (fun x => propAngv x i) t).
    Proof. intros. unfold thrust, onePropThrust. v2e (propAngv t). cbv. ra. Qed.

    (* 各个桨的旋转对机体力矩的贡献
       桨1,3逆时针转，产生顺时针的反作用力，使飞行器顺时针转；
       桨2,4顺时针转，产生逆时针的反作用力，使飞行器逆时针转；
       桨1的升力使x轴正转，y轴正转，力臂为 (√2/2)*d，力矩使z轴正转
       桨2的升力使x轴反转，y轴正转，力臂为 (√2/2)*d，力矩使z轴反转
       桨3的升力使x轴反转，y轴反转，力臂为 (√2/2)*d，力矩使z轴正转
       桨4的升力使x轴正转，y轴反转，力臂为 (√2/2)*d，力矩使z轴反转 *)
                        
    (** 螺旋桨在xb轴上产生的滚转力矩 *)
    Definition torquex (t : R) :=
      (sqrt 2) / 2 * d * c_T * ((ϖ1 t)² - (ϖ2 t)² - (ϖ3 t)² + (ϖ4 t)²).
    (** 螺旋桨在yb轴上产生的俯仰力矩 *)
    Definition torquey (t : R) :=
      (sqrt 2) / 2 * d * c_T * ((ϖ1 t)² + (ϖ2 t)² - (ϖ3 t)² - (ϖ4 t)²).
    (** 螺旋桨在zb轴上产生的偏航力矩 *)
    Definition torquez (t : R) :=
      (c_M * ((ϖ1 t)² - (ϖ2 t)² + (ϖ3 t)² - (ϖ4 t)²))%R.
    Notation τx := torquex.
    Notation τy := torquey.
    Notation τz := torquez.

    (* 合并拉力和力矩，构造统一的控制效率模型矩阵 *)

    (** 拉力和力矩构成的向量 [f;τx;τy;τz] *)
    Definition thrustTorque (t : R) : vec 4 := l2v [thrust t; τx t; τy t; τz t].
    (** 螺旋桨旋转角速度平方的向量 [ϖ1²;ϖ2²;ϖ3²;ϖ4²] *)
    Definition propAngvSquare (t : R) : vec 4 :=
      l2v [(ϖ1 t)²; (ϖ2 t)²; (ϖ3 t)²; (ϖ4 t)²].
    (** 由螺旋桨旋转角速度计算拉力和力矩的控制效率矩阵  *)
    Definition controlMat : smat 4 :=
      let dcT2 := d * c_T * ((sqrt 2) / 2) in
      l2m [[c_T; c_T; c_T; c_T];
           [dcT2; - dcT2; - dcT2; dcT2];
           [dcT2; dcT2; - dcT2; - dcT2];
           [c_M; - c_M; c_M; - c_M]]%R.

    (** 控制效率模型 *)
    Lemma thrustTorque_eq : forall t, thrustTorque t = controlMat *v propAngvSquare t.
    Proof.
      intros. unfold thrustTorque, controlMat, propAngvSquare.
      unfold thrust, torquex, torquey, torquez. v2e (propAngv t). veq; try lra.
    Qed.
  End thrust_torque.
End XQuadThrustTorque.

(** *** 多旋翼的拉力力矩模型 *)
Module MulticopterThrustTorque.
  Open Scope R_scope.
  Section thrust_torque.
    (** 无人机全局固有参数的缩写，为了简化输入 *)
    Let c_T := Config.c_T.
    Let c_M := Config.c_M.

    (** 假设共有n个螺旋桨，按顺时针方向从i=1到i=n依次标记螺旋桨 *)
    Variable n : nat.
    (** 假设obxb轴与每个桨所在的支撑臂的夹角为 φ_i *)
    Variable armAngles : vec n.
    Notation φ := armAngles.
    (** 假设机体中心与第i个电机的距离为d_i *)
    Variable d : vec n.

    (** 各螺旋桨的转速 (rad/s) *)
    Variable propAngv : R -> vec n.
    Notation ϖ := propAngv.

    (** 作用在该旋翼上的总拉力 f = ∑T_i *)
    Definition thrust (t : R) : R := vsum (fun i => c_T * (ϖ t i)²).

    (* 各个桨的旋转对机体力矩的贡献
       奇数编号的桨逆时针转，产生顺时针的反作用力，使飞行器顺时针转，力矩使z轴正转；
       偶数编号的桨顺时针转，产生逆时针的反作用力，使飞行器逆时针转，力矩使z轴反转；
       每个桨的升力对x轴的翻滚力矩和y轴的俯仰力矩分析：
       1. 升力对x轴产生负力矩，力臂是 sin φ_i
       2. 升力对y轴产生正力矩，力臂是 cos φ_i *)

    (** 第 i 个 (i = 1, ..., n) 螺旋桨产生的对 zb 轴的反扭力矩的方向 *)
    Definition delta (i : 'I_n) : R :=
      (* 注意，fin2nat i 是从0开始，所以要 +1 才是需要的 1, ..., 2 *)
      let id := S i in
      if Nat.odd id then 1 else -1.
                        
    (** 螺旋桨在xb轴上产生的滚转力矩 *)
    Definition torquex (t : R) : R :=
      vsum (fun i => - (d i) * sin (φ i) * (c_T * (ϖ t i)²)).
    (** 螺旋桨在yb轴上产生的俯仰力矩 *)
    Definition torquey (t : R) : R :=
      vsum (fun i => (d i) * cos (φ i) * (c_T * (ϖ t i)²)).
    (** 螺旋桨在zb轴上产生的偏航力矩 *)
    Definition torquez (t : R) := vsum (fun i => c_M * (delta i * (ϖ t i)²)).
    Notation τx := torquex.
    Notation τy := torquey.
    Notation τz := torquez.

    (* 合并拉力和力矩，构造统一的控制效率模型矩阵 *)

    (** 拉力和力矩构成的向量 [f;τx;τy;τz] *)
    Definition thrustTorque (t : R) : vec 4 := l2v [thrust t; τx t; τy t; τz t].
    (** 螺旋桨旋转角速度平方的向量 [ϖ1²; ... ; ϖn²] *)
    Definition propAngvSquare (t : R) : vec n := fun i => (ϖ t i)².
    (** 由螺旋桨旋转角速度计算拉力和力矩的控制效率矩阵  *)
    Definition controlMat : mat 4 n :=
      fun i j => match fin2nat i with
               | 0 => c_T
               | 1 => - (d j) * c_T * sin (φ j)
               | 2 => (d j) * c_T * cos (φ j)
               | 3 => c_M * (delta j)
               | _ => 0
               end.

    (** 控制效率模型 *)
    Lemma thrustTorque_eq : forall t, thrustTorque t = controlMat *v propAngvSquare t.
    Proof.
      intros. unfold thrustTorque, controlMat, propAngvSquare.
      unfold thrust, torquex, torquey, torquez.
      apply veq_iff_vnth; intros.
      rewrite vnth_l2v. rewrite vnth_mmulv. simpl.
      destruct i. simpl. unfold vdot, Vector.vdot. unfold vsum.
      destruct i; [f_equal | try lia].
      destruct i; [f_equal | try lia]. apply veq_iff_vnth; intros; cbv; lra.
      destruct i; [f_equal | try lia]. apply veq_iff_vnth; intros; cbv; lra.
      destruct i; [f_equal | try lia]. apply veq_iff_vnth; intros; cbv; lra.
    Qed.
  End thrust_torque.
End MulticopterThrustTorque.



(* ######################################################################### *)
(** * 动力单元模型 *)

(* 涉及到：传递函数、拉式变换，我可能还无法形式化它们 *)

