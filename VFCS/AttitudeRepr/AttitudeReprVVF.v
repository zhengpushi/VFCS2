(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Attitude Representation for FCS (使用了向量值函数、矩阵函数的版本)
  author    : Zhengpu Shi
  date      : Mar, 2021
  
  reference :
  * QuanQuan, UAV design and control, page 90-106
  
  remark    :
  * coordinate frame
    Earth-Fixed Coordinate Frame, 地球固连坐标系，记作{e}
    Aircraft-Body Coordinate Frame, 机体坐标系，记作 {b}
    Intermediate Coordinate Frame k, 中间坐标系 {k}
    Intermediate Coordinate Frame n, 中间坐标系 {n}
  
 *)

From FinMatrix Require Import MatrixR.

Require Export Calculus.
(* 向量值函数、矩阵函数，进一步的封装，有利有弊 *)
Require Export DifferentialVVF.
Require Export DifferentialMVF.

From OrienRepr Require Export Pose.
From FinMatrix Require Export MatrixR.

Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.
Open Scope VecValFun_scope.
Open Scope MatValFun_scope.

(** Convert (fun x => f x) ' to f ' *)
Ltac eta_Derive :=
  repeat
    match goal with
    | |- context[ (fun x => ?f x) '] => replace ((fun x => f x)') with (f '); auto
    end.


(* 右手定则的惯例
   1. 确定坐标轴：右手拇指指向x轴正方向，食指指向y轴正方向，中指指向z轴正方向。
   2. 确定旋转正方向：右手大拇指指向轴的正方向，弯曲四指的方向即是旋转正方向。*)

(* 坐标系
   1. 地球固联坐标系：忽略地球曲率，将地球表面假设称一张平面。通常以多旋翼起飞位置
      作为坐标原点 $o_e$，让$x_e$轴在水平面内指向某一方向，$z_e$轴垂直于地面向下，
      然后按右手定则确定$y_e$轴。
   2. 机体坐标系：与多旋翼固连，原点$o_b$取在多旋翼的中心位置，$x_b$轴在多旋翼对称平面
      内指向机头（对于四旋翼，又有十字形或X形两种方式）。$z_b$轴在飞机对称平面内，
      垂直$x_b$轴向下。然后按右手定则确定$y_b$轴。
   3. 用下标e表示Earth，下标b表示Body，这两个坐标系分别记作{e}和{b}
   4. 如果要表示向量相对于某坐标系的坐标，则放在左上角。
      例如，相对于{e}而言$x_b$的单位向量(也称方向向量)是 ${}^e b_x$。 *)

(* 从欧拉角到旋转矩阵，以及欧拉角变化率与机体角速度的转换矩阵 *)
Section eulerAngles.

  (* 
    欧拉角与旋转矩阵
    1. 请参考 https://en.wikipedia.org/wiki/Rotation_matrix#Ambiguities 了解旋转歧义性
       旋转分为主动旋转和被动旋转，我们采用主动旋转。
       基本旋转矩阵 Rx,Ry,Rz，全老师书上是转置形式，应该是被动旋转。
       关于SO(3) 和基本旋转矩阵的各种性质，在 OrienRepr 项目中。
    2. {b}与{e}之间的夹角就是飞机的姿态角，又称欧拉角，见全老师书上的插图5.5。
       * 欧拉角在{e}中的直观定义：
         机体坐标系与地面惯性坐标系之间的夹角就是飞机的姿态角，又称欧拉角。
         (1) 俯仰角θ： 机体轴与地平面（水平面）之间的夹角，飞机抬头为正。
         (2) 偏航角（方位角）ψ：机体轴在水平面上的投影与地轴之间的夹角，以机头右偏为正。
         (3) 滚转角（倾斜角）ϕ：飞机对称面绕机体轴 转过的角度，右滚为正。 
       * 欧拉角作为过程量的定义规则，我们采用 “ZYX欧拉角” 定义：
         (1) 初始时，{b}和{e}重合；
         (2) 将{b}绕b_z轴旋转ψ(称偏航角yaw)到达{k}；
         (3) 将{k}绕k_y轴旋转θ(称俯仰角pitch)到达{n}；
         (4) 将{n}绕n_z轴旋转ϕ(称滚转角roll)到达{b}。
         以上过程有两种理解方式，见 https://blog.csdn.net/a735148617/article/details/116740453
         (1) RPY角：指绕惯性坐标系旋转（即，绕的轴在整个旋转中是固定不变的），依次绕
             X轴（roll角），Y轴（pitch角），Z轴（yaw角）进行旋转
         (2) ZYX角：指绕刚体固连坐标系旋转（即，绕的轴会随着旋转变化而变化），依次绕
             z轴（yaw角），旋转后的y'轴（pitch角），两次旋转后的x''轴（roll角）进行旋转。
         这里的方式(1)称为XYZ外旋，方式(2)称为 z-y'-x''内旋。
         注意，这两种旋转是完全等价的，即若roll,pitch,yaw取相同的指，按这两种过程进行旋转，
         得到的结果相同。
   *)

  (* 相对于坐标系{e}的自身三个轴的单位向量，它们是由时间而定的向量值函数 *)
  Definition b_b1 : vvf 3 := fun t => v3i.
  Definition b_b2 : vvf 3 := fun t => v3j.
  Definition b_b3 : vvf 3 := fun t => v3k.
  Hint Unfold b_b1 b_b2 b_b3 : fcs.

  (* 相对于坐标系{e}的自身三个轴的单位向量 *)
  Definition e_e1 : vvf 3 := fun t => v3i.
  Definition e_e2 : vvf 3 := fun t => v3j.
  Definition e_e3 : vvf 3 := fun t => v3k.
  Hint Unfold e_e1 e_e2 e_e3 : fcs.

  (* 坐标系{n}的y轴相对于{n}的单位向量 *)
  Definition n_n2 : vvf 3 := fun t => v3j.
  (* 坐标系{k}的z轴相对于{k}的单位向量 *)
  Definition k_k3 : vvf 3 := fun t => v3k.
  Hint Unfold n_n2 k_k3 : fcs.

  (* 设欧拉角(姿态角)如下 *)
  Variable eulerAngles : vvf 3. Notation Φ := eulerAngles.
  Notation ϕ := (Φ.1). (* 绕 x 轴旋转的滚转角 roll *)
  Notation θ := (Φ.2). (* 绕 y 轴旋转的俯仰角 pitch *)
  Notation ψ := (Φ.3). (* 绕 z 轴旋转的偏航角 yaw *)
  Notation dΦ := (vvfderiv Φ). (* 欧拉角变化率 *)

  (* 根据欧拉角的定义，{b}相对于{n}, {n}相对于{k}, {k}相对于{e} 的位姿如下 *)
  Definition R_b2n : smvf 3 := fun t => Rx (ϕ t).
  Definition R_n2k : smvf 3 := fun t => Ry (θ t).
  Definition R_k2e : smvf 3 := fun t => Rz (ψ t).
  Hint Unfold R_b2n R_n2k R_k2e : fcs.

  (* 由于每一次旋转都是绕物体坐标系，所以矩阵连乘符合右乘。
     所以，{b}相对{e}的位姿如下 *)
  Definition R_b2e : smvf 3 := R_k2e * R_n2k * R_b2n.
  Hint Unfold R_b2e R_n2k R_k2e : fcs.

  (* 还能给出如下中间信息，在后面推导机体角速度与姿态角变化率时用到 *)
  Definition R_n2b : smvf 3 := R_b2n\T.
  Definition R_k2n : smvf 3 := R_n2k\T.
  Definition R_k2b : smvf 3 := R_n2b * R_k2n.
  Definition b_n2 : vvf 3 := R_n2b *v n_n2.
  Definition b_k3 : vvf 3 := R_k2b *v k_k3.
  Hint Unfold R_n2b R_k2n R_k2b b_n2 b_k3 : fcs.

  (* 我们可以给出 R_b2e 的实矩阵形式（无时间变量，无unicode字符）以便指导编程 *)
  Definition b2eMAT (roll pitch yaw : R) : smat 3 :=
    let s1 := sin roll in
    let c1 := cos roll in
    let s2 := sin pitch in
    let c2 := cos pitch in
    let s3 := sin yaw in
    let c3 := cos yaw in
    l2m [[c3 * c2; c3 * s2 * s1 - c1 * s3; c3 * s2 * c1 + s1 * s3];
         [s3 * c2; s3 * s2 * s1 + c1 * c3; s3 * s2 * c1 - s1 * c3];
         [- s2; c2 * s1; c2 * c1]]%R.

  (* 验证上述矩阵正确 *)
  Lemma b2eMAT_spec : forall t, b2eMAT (ϕ t) (θ t) (ψ t) = R_b2e t.
  Proof.
    intros. autounfold with fcs. autounfold with mvf vvf.
    vvf2e eulerAngles. meq; lra.
  Qed.

  (* 从旋转矩阵到欧拉角，在 OrienRepr 项目中。此处略 *)

  (* 机体(旋转的)角速度（angular velocity of the aircraft）与
     姿态角变化率（attitude rate）的关系 *)
  (* Section eulerAngleRate_and_angularVelocity. *)
  (* 1. 推导过程的来源
          (1) 全老师的书，可惜的是基本旋转矩阵是转置的，需要多理解
          (2) https://blog.csdn.net/weixin_45910027/article/details/134247958
          (3) https://blog.csdn.net/a735148617/article/details/116740453
       2. 机体角速度 ω 是指机体相对于{e}的三个坐标轴的旋转角度的变化。
          机体角速度 ω_b 是指机体相对于{e}的三个坐标轴的角度变化在{b}中的表达。
           姿态角速率 Φ̇ 是指指欧拉角（随时间变化的函数）的导数
       3. 机体坐标系的三个角速度分量，是机体坐标系相对于地面坐标的转动角速度在机体坐标系
   *)

  (* 设机体角速度在{b}中的表示如下，三个分量也记作 p,q,r *)
  Variable b_angv : vvf 3. Notation b_ω := b_angv.
  (* Notation b_ωx := (b_ω.1). (* 角速度在xb轴上的分量 *) *)
  (* Notation b_ωy := (b_ω.2). (* 角速度在yb轴上的分量 *) *)
  (* Notation b_ωz := (b_ω.3). (* 角速度在zb轴上的分量 *) *)
  
  (* 根据相关理论，机体角速度与姿态角速率的关系如下 *)
  Axiom H_b_ω : forall t,
      b_ω t = (ϕ ' t s* b_b1 t
                + θ ' t s* b_n2 t
                + ψ ' t s* b_k3 t)%V.

  (* n2 轴在 {b} 中的向量具有以下形式 *)
  Lemma b_n2_eq : forall t, b_n2 t = l2v [0; cos (ϕ t); - sin (ϕ t)]%R.
  Proof.
    intros. autounfold with fcs. autounfold with mvf vvf.
    vvf2e eulerAngles. veq; lra.
  Qed.

  (* k3 轴在 {b} 中的向量具有以下形式 *)
  Lemma b_k3_eq : forall t,
      b_k3 t = l2v [- sin (θ t); cos (θ t) * sin (ϕ t); cos (θ t) * cos (ϕ t)]%R.
  Proof. intros. veq; lra. Qed.

  (* 从欧拉角速率到机体角速度的转换矩阵（无时间变量，无unicode字符），以便指导编程 *)
  Definition eulerRate2angvMAT (roll pitch : R) : smat 3 :=
    let s1 := sin roll in
    let c1 := cos roll in
    let s2 := sin pitch in
    let c2 := cos pitch in
    l2m [[1; 0; - s2];
         [0; c1; s1 * c2];
         [0; - s1; c1 * c2]]%R.

  (* 该矩阵满足如下规范 *)
  Lemma eulerRate2angvMAT_spec : forall t,
      b_ω t = ((eulerRate2angvMAT (ϕ t) (θ t)) *v dΦ t)%M.
  Proof.
    intros. rewrite H_b_ω. autounfold with fcs. autounfold with mvf vvf.
    vvf2e eulerAngles. vvf2e b_angv. veq; eta_Derive; ra.
  Qed.

  (* 从机体角速度到欧拉角速率的转换矩阵（无时间变量，无unicode字符），以便指导编程 *)
  Definition angv2eulerRateMAT (roll pitch : R) : smat 3 :=
    let s1 := sin roll in
    let c1 := cos roll in
    let s2 := sin pitch in
    let c2 := cos pitch in
    let t2 := tan pitch in
    l2m [[1; t2 * s1; t2 * c1];
         [0; c1; - s1];
         [0; s1 / c2; c1 / c2]]%R.

  (* 俯仰角的正常范围 θ∈(-π/2,π/2) 内，此时，0 < cos θ *)
  Definition pitchValid (pitch : R) : Prop := - (PI / 2) < pitch < PI / 2.

  (* 当俯仰角在正常范围内时，余弦值非零 *)
  Lemma pitchValid_cos_pitch_neq0 : forall pitch, pitchValid pitch -> cos pitch <> 0.
  Proof. intros. hnf in H. logic. apply Rgt0_neq0. apply cos_gt_0; auto. Qed.

  (* angv2eulerRateMat 和 eulerRate2angvMAT 的乘积为单位阵，即它们互逆 *)
  Lemma mmul_angv2eulerRateMAT_eulerRate2angvMAT_eq1 : forall roll pitch,
      pitchValid pitch ->
      (angv2eulerRateMAT roll pitch * eulerRate2angvMAT roll pitch = mat1)%M.
  Proof.
    intros. meq; ra.
    all: try rewrite tan_eq; field_simplify_eq; ra.
    all: apply pitchValid_cos_pitch_neq0; auto.
  Qed.
  
(* cos_gt_0: forall x : R, - (PI / 2) < x -> x < PI / 2 -> 0 < cos x *)

  (* 该矩阵满足如下规范，这即是欧拉角模型 *)
  Lemma angv2eulerRateMAT_spec : forall t,
      pitchValid (θ t) ->
      dΦ t = (angv2eulerRateMAT (ϕ t) (θ t) *v b_ω t)%M.
  Proof.
    intros. rewrite eulerRate2angvMAT_spec. rewrite <- mmulv_assoc.
    rewrite mmul_angv2eulerRateMAT_eulerRate2angvMAT_eq1; auto.
    rewrite mmulv_1_l; auto.
  Qed.
  
End eulerAngles.

(* ocaml代码抽取测试 *)
Extraction "ocaml_attitudeRepr.ml" b2eMAT eulerRate2angvMAT angv2eulerRateMAT m2l.

(* 
  1. 从欧拉角到旋转矩阵
  * 使用在线网站 https://www.andre-gaschler.com/rotationconverter/ 为例，
    在 Euler angles of multiple axis rotations (radians) 中输入
    ZYX方式，x=0.1, y=0.2, z=0.3，得到 Rotation matrix 如下：
[  0.9362934, -0.2750959,  0.2183507;
   0.2896295,  0.9564251, -0.0369570;
  -0.1986693,  0.0978434,  0.9751703 ]
  * 在ocaml环境中得到如下结果
utop[1]> m2l 3 3 (b2eMAT 0.1 0.2 0.3);;
- : float list list =
[[0.936293363584199234; -0.275095847318243714; 0.218350663146334445];
 [0.289629477625515552; 0.95642508584923247; -0.0369570135246250833];
 [-0.198669330795061216; 0.0978433950072557096; 0.975170327201816]]
 *)

(* 理解机体角速度向量 ωb
   1. 这是表示物体绕其质心旋转速率和旋转轴的向量。
      它是一个三维向量，通常用角速度的分量来表示，例如在 x、y 和 z 轴上的角速度。
      角速度向量的方向通常与旋转轴的方向相同，其大小表示旋转的速率。
   2. 对于角速度向量，范数 ∥ωb∥ 表示物体旋转的总速率，不考虑旋转轴的方向。
   3. 角速度向量与飞行器的姿态（例如，通过欧拉角或四元数表示）密切相关。
      通过积分角速度向量或使用更复杂的滤波器（如卡尔曼滤波器），可以从角速度估计出姿态。
 *)
(* 旋转矩阵导数和机体角速度之间的关系 *)
Section derivRotMat_and_angv.
  (* 设机体角速度在{b}中的表示为 *)
  Variable b_angv : vvf 3. Notation b_ω := b_angv.

  (* 设{b}相对于{e}的旋转矩阵为 *)
  Variable Rb2e : smvf 3.
  (* 旋转矩阵还要满足 SO(3) 的性质 *)
  Hypotheses Rb2e_SO3 : forall t, SOnP (Rb2e t).
  
  (* 机体角速度在 {e} 中的表示为 *)
  Let e_ω : vvf 3 := Rb2e *v b_ω.

  (* 任意 {e} 中的向量 e_r 的导数满足如下关系式 *)
  Axiom H_deriv_e_r : forall (e_r : vvf 3), vvfderiv e_r = e_ω \x e_r.
  
  (* 反对称矩阵和叉乘有关的理论已经开发完毕，例如 *)
  (* Check v3cross_eq_skew_mul_vec. *)
  (* : forall a b : vec 3, a \x b = `| a |x *v b *)

  (* Rb2e的导数满足如下关系 *)
  Lemma derivRb2e_eq_e_ω : mvfderiv Rb2e = mvfskew3 e_ω * Rb2e.
  Proof.
    rewrite mvfderiv_eq_vvfderiv_col.
    extensionality t. extensionality i. extensionality j.
    rewrite H_deriv_e_r. autounfold with mvf vvf.
    rewrite v3cross_eq_skew_mul_vec. auto.
  Qed.
    
  (* 旋转矩阵的导数和机体角速度之间的关系如下，该关系式用于控制器的设计 *)
  Lemma derivRb2e_eq : mvfderiv Rb2e = Rb2e * mvfskew3 b_ω.
  Proof.
    rewrite derivRb2e_eq_e_ω. unfold e_ω. autounfold with mvf vvf.
    (* 证明 (skew3 [e_ω]) * Rb2e = Rb2e * skew3 [b_ω]
       左 = skew3 [Rb2e * b_ω] * Rb2e
          = (Rb2e * skew3 b_ω * Re2b) * Rb2e        这是SO3的矩阵才有的特性
          = Rb2e * skew3 b_ω *)
    extensionality t. rewrite <- SO3_skew3_eq; auto. rewrite mmul_assoc.
    assert (morth (Rb2e t)) by apply Rb2e_SO3.
    rewrite morth_iff_mul_trans_l in H. rewrite H. rewrite mmul_1_r. auto.
  Qed.
End derivRotMat_and_angv.

(* 四元数的基本理论，四元数与旋转矩阵、轴角等的转换，在 OrienRepr 项目中。此处略 *)

(* 当 x 足够小时，可以有如下结论：cos x ≈ 1, sin x ≈ x 。因为：
   cos x ≈ 1 - (1/2) x² + O (x⁴)
   sin x ≈ x - (1/6) x³ + O (x⁵) *)
(* 定义一个属性来描述 x 是非常小的 *)
Definition is_small (x : R) : Prop := x < 1e-3.
Axiom Small_x_Cosine : forall x : R, is_small x -> cos x = 1.
Axiom Small_x_Sine : forall x : R, is_small x -> sin x = x.


(* 四元数导数与机体角速度的关系 *)
Section derivQuat_and_angv.

  (* 四元数函数的导数，也就是向量的导数。见 vderiv *)

  (* 设 {e} 相对于 {b} 的四元数如下，它随时间而变化。注意，不是 {b} 相对于 {e} *)
  Variable q_e2b : R -> quat.
  
  (* 设机体角速度在{b}中的表示如下 *)
  Variable b_angv : vvf 3. Notation b_ω := b_angv.
  (* 假设角速度向量非零 *)
  Hypotheses H_b_ω_neq0 : forall t, b_ω t <> vzero.

  (* 推导从 t 到 t + Δt 而发生微小摄动时的四元数变化 *)
  Section deltaQuat.
    (* 任意的四元数函数 *)
    Variable q : R -> quat.
    (* 任意小的时间间隔 *)
    Variable deltaT : R.
    Notation Δt := deltaT.

    (* 首先，定义 Δt 对应的旋转摄动的四元数 *)
    
    (* 定义旋转角，其直观含义是：时间越长，则旋转角越大 *)
    Let rotAngle : R -> R := fun t => (vlen (b_ω t) * Δt)%R.
    Notation θ := rotAngle.
    (* 定义旋转轴 *)
    Let rotAxis : vvf 3 := fun t => vnorm (b_ω t).
    (* 定义旋转摄动 Δq *)
    Definition deltaQuat (t : R) : quat := aa2quat (mkAA (θ t) (rotAxis t)).
    
    (* 当Δt足够小时，Δq可简化为简单的表达式 *)
    Lemma deltaQuat_eq : forall t,
        (* 注意这个特殊的前提，并不是 is_small Δt，它不足以完成证明。
           这个前提也说明了此处的简化不适用于大机动飞行的情形，因为那样的化
           角速度的范数会很大，不满足小范围假设 *)
        is_small (||b_ω t|| * Δt / 2) ->
        deltaQuat t = si2q 1 (((1/2) * deltaT)%R s* b_ω t)%V.
    Proof.
      intros. unfold deltaQuat. unfold aa2quat. unfold rotAngle, rotAxis.
      rewrite Small_x_Sine, Small_x_Cosine; auto.
      f_equal. unfold vnorm. rewrite vscal_assoc.
      f_equal. autounfold with tA. field.
      apply vlen_neq0_iff_neq0. auto.
    Qed.
  End deltaQuat.

  (* 假设 t + Δt 后的四元数与 t 时刻的四元数有如下关系。
     ToDo: 根据坐标系旋转的复合四元数来推导，不要作为假设 *)
  Axiom quat4AddDelta : forall deltaT t,
      q_e2b (t + deltaT) = (q_e2b t * deltaQuat deltaT t)%quat.

  (** 四元数变化率与机体角速度的关系 *)
  Lemma derivQuat_eq :
    (forall t h, is_small ((||b_ω t||) * h / 2)) ->
    vvfderiv q_e2b =
      fun t =>
        ((1/2) s*
           (mconsrH (vconsH 0 (- b_ω t)%V)
              (mconscH (b_ω t) (- (skew3 (b_ω t)))%M)) *v  (q_e2b t))%V.
  Proof.
    intros.
    unfold vderiv. extensionality t. extensionality i.
    lazy [Derive].          (* 将导数转换为极限 *)
    remember (mconsrH (vconsH 0 (- b_ω t)%V)
                (mconscH (b_ω t) (- (skew3 (b_ω t)))%M)) as A.
    rewrite Lim_ext with (f:=fun h => ((((1/2) s* A)%M *v q_e2b t) i * (h / h))%R).
    - rewrite Lim_scal_l.
      rewrite Lim_ext with (f:=fun _ => 1).
      rewrite Lim_const. simpl. ra. rewrite mmulv_mscal. auto.
      intros. ra.
      (* 如何避免 h <> 0 的这个证明？ *)
      admit.
    - intros. unfold Rdiv. rewrite <- Rmult_assoc. f_equal.
      rewrite quat4AddDelta. rewrite deltaQuat_eq; auto. unfold si2q.
      rewrite HeqA. rewrite qmatR_spec2. rewrite qmatR_spec1.
      rewrite vnth_vconsH_0. rewrite mscal_1_l.
      2:{ cbv. fin. }
      rewrite mmulv_madd. rewrite mmulv_1_l.
      unfold q2im. rewrite vremoveH_vconsH; fin.
      rewrite vnth_vadd. unfold Rminus.
      rewrite associative. rewrite (commutative _ (- q_e2b t i)%R).
      rewrite <- associative. rewrite Rplus_opp_r. rewrite Rplus_0_l.
      rewrite !mscal_mconsrH. rewrite !vscal_vconsH. ra.
  Abort.
  
  Lemma derivQuat_eq :
    (forall t h, is_small ((||b_ω t||) * h / 2)) ->
    vderiv q_e2b =
      fun t =>
        ((1/2) s*
           (mconsrH (vconsH 0 (- b_ω t))
              (mconscH (b_ω t) (- (skew3 (b_ω t)))%M)) *v  (q_e2b t))%V.
  Proof.
    intros.
    unfold vderiv. extensionality t. extensionality i.
    lazy [Derive].          (* 将导数转换为极限 *)
    remember (mconsrH (vconsH 0 (- b_ω t)%V)
                (mconscH (b_ω t) (- (skew3 (b_ω t)))%M)) as A.
    rewrite Lim_ext with (f:=fun h => ((((1/2 * h)%R s* A)%M *v q_e2b t) i) / h).
    - (* 再替换一次 *)
      rewrite Lim_ext with (f:=fun h => (((1/2) s* A)%M *v q_e2b t) i).
      + rewrite Lim_const. rewrite mmulv_mscal. auto.
      + intros h.
        replace (1 / 2 * h)%R with (h * (1 / 2))%R by lra. 
        rewrite <- mscal_assoc.
        unfold Rdiv at 2. rewrite Rmult_comm.
        rewrite <- vnth_vscal.
        rewrite <- mmulv_mscal. f_equal.
        rewrite !mscal_assoc. f_equal. cbv. field.
        (* 如何避免 h <> 0 的这个证明？ *)
        admit.
    - intros h. f_equal.
      rewrite quat4AddDelta. rewrite deltaQuat_eq; auto. unfold si2q.
      rewrite HeqA. rewrite qmatR_spec2. rewrite qmatR_spec1.
      rewrite vnth_vconsH_0. rewrite mscal_1_l.
      2:{ cbv. fin. }
      rewrite mmulv_madd. rewrite mmulv_1_l.
      unfold q2im. rewrite vremoveH_vconsH; fin.
      rewrite vnth_vadd. unfold Rminus.
      rewrite associative. rewrite (commutative _ (- q_e2b t i)%R).
      rewrite <- associative. rewrite Rplus_opp_r. rewrite Rplus_0_l.
      rewrite !mscal_mconsrH. rewrite !vscal_vconsH. ra. f_equal. f_equal.
      + f_equal. rewrite vscal_vopp. auto.
      + rewrite mscal_mconscH. f_equal.
        rewrite mscal_mopp. f_equal. rewrite skew3_vscal. auto.
  Admitted.

  (* 备注：在实际中，b_ω 可由陀螺仪近似测得，此时以上微分方程为线性的。*)

  (* 可以给出 W 分量 和 Im 分量的导数形式 *)

  Let q0 := fun t => (q_e2b t).W.
  Let qv := fun t => (q_e2b t).Im.

  (** 四元数W分量q0的导数与机体角速度b_ω的关系 *)
  Lemma derivQuat_W_eq :
    (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
    q0 ' = fun t => <((-(1/2))%R s* qv t)%V, b_ω t>.
  Proof.
    intros. unfold q0,qv.
    pose proof (derivQuat_eq). rewrite fun_eq_iff_forall_eq in H0.
    extensionality t. specialize (H0 H t).
    rewrite veq_iff_vnth in H0. specialize (H0 #0).
    unfold vderiv in *. rewrite H0.
    (* Tips: 展示矩阵证明的复杂推理步骤的一个很好的例子 *)
    (* 直接计算就能完成证明 *)
    q2e (q_e2b t). v2e (b_angv t). cbv. ra.
    (* 或者，用性质来化简，也反映出证明过程 *)
    (* rewrite vnth_vscal. rewrite vdot_vscal_l. rewrite vnth_mmulv. *)
    (* unfold mconsrH. unfold Matrix.mconsrH. *)
    (* rewrite Vector.vnth_vconsH_0; fin. *)
    (* 继续开发 vconsH 和 vdot 的性质，略 *)
  Qed.

  (** 四元数Im分量qv的导数与机体角速度b_ω的关系 *)
  Lemma derivQuat_Im_eq :
    (forall t h : R, is_small ((||b_ω t||) * h / 2)) ->
    vderiv qv = fun t => ((1/2) s* (q0 t s* mat1 + skew3 (qv t))) *v (b_ω t).
  Proof.
    intros. unfold q0,qv.
    pose proof (derivQuat_eq). rewrite fun_eq_iff_forall_eq in H0.
    extensionality t. specialize (H0 H t).
    rewrite veq_iff_vnth in H0.
    unfold vderiv in *. unfold q2im.
    apply veq_iff_vnth. intros i.
    unfold vremoveH. unfold Vector.vremoveH. rewrite H0. clear.
    v2e (b_ω t). q2e (q_e2b t).
    destruct i.
    repeat (destruct i; [cbv; lra| try lia]).
  Qed.

End derivQuat_and_angv.
