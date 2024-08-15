(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Entry of Propulsion Subsystem
  author    : Zhengpu Shi
  date      : Jun, 2024

  reference : 
  1. Introduction to Multicopter Design and Control, QuanQuan, 2017

  remark    :
 *)

From FinMatrix Require Import MatrixR.
(* Require PSModel PSExtension. *)
Open Scope R_scope.

(* 
   对多旋翼建模时，做如下假设：
   1. 多旋翼是刚体
   2. 质量和转动惯量不变
   3. 多旋翼几何中心与重心一致
   4. 多旋翼只受重力和螺旋桨拉力，其中，
      重力沿o_ez_e轴正方向，螺旋桨拉力沿o_bz_b轴负方向
   5. 奇数标号的螺旋桨为逆时针转动，偶数标号的螺旋桨为顺时针转动。
 *)

(* 旋翼数目 *)
Inductive RotorCount :=
| RotorCount4       (* 四旋翼 *)
| RotorCount6       (* 六旋翼 *)
.

(* 四旋翼的两种机头方向 *)
Inductive QuadcopterHead :=
| QHeadPLUS         (* +字型 *)
| QHeadCross        (* x字型 *)
.

(** 第i个(i=1,2,...,nr)螺旋桨的旋转方向对应的实数值：
    奇数标号是逆时针取-1，偶数标号是顺时针取+1 *)
Definition rotDir2val (i : nat) : R := if Nat.odd i then (-1) else 1.

(** 下一个桨的旋转方向总是与这个桨的旋转方向相反 *)
Lemma rotDir2val_S : forall i, rotDir2val (S i) = Ropp (rotDir2val i).
Proof.
  intros. unfold rotDir2val.
  replace (Nat.odd (S i)) with (negb (Nat.odd i)).
  destruct (Nat.odd i); auto. cbv. lra.
  rewrite Nat.negb_odd. rewrite Nat.odd_succ. auto.
Qed.

(** 多旋翼的配置，即不变的一些参数 *)
Module Config.

  (** 旋翼数目（暂未采用) *)
  Parameter rotorCount : RotorCount.

  (** 旋翼数目的自然数值 *)
  Parameter rotorCountNat : nat.
  Axiom rotorCountNat_gt0 : (0 < rotorCountNat)%nat.  (* 至少1个桨 *)

  (** 重力加速度 (m/s²) *)
  Parameter g : R.
  Axiom g_gt0 : 0 < g.          (* g是正值 *)

  Lemma g_neq0 : g <> 0.
  Proof. pose proof g_gt0. lra. Qed.

  (** 整机质量 (kg) *)
  Parameter m : R.
  Axiom m_gt0 : 0 < m.

  Lemma m_neq0 : m <> 0.
  Proof. pose proof m_gt0. lra. Qed.

  (** 总转动惯量（Moment of Inertia），记作J:
     J 是一个 3×3 的矩阵，表示整个多旋翼飞行器相对于其质心的转动惯量。
     这个矩阵考虑了飞行器所有部件（包括机身、电机、螺旋桨、电池等）的质量分布对
     转动惯量的贡献。
     对角线上的元素 Jxx,Jyy,Jzz 分别表示飞行器绕 x, y 和 z 轴的转动惯量。
     非对角线上的元素表示飞行器各轴之间的耦合转动惯量，也称为积惯量。
     它通常被视为常数，但在某些情况下可能会变化，比如：飞行器携带的有效载荷发生变化
     （例如增加或减少电池、摄像头等），或者飞行器结构发生改变（如损坏或维修）。
     此时，需要重新计算或测量 J 矩阵。 *)
  Parameter J : smat 3.

  (** 电机转子和螺旋桨绕转轴轴的总转动惯量 (rotor-propeller ..)，记作 J_{RP}:
     JRP 是一个实数，表示一组整个电机转子和螺旋桨绕其转轴的总转动惯量。
     这个矩阵主要用于描述每个电机及其螺旋桨的旋转运动对飞行器动力学的影响。
     JRP 的值取决于螺旋桨的质量、形状、大小以及电机转子的特性。
     它通常被视为常数，但在某些情况下可能会变化，比如：螺旋桨因磨损、损坏或更换等原因
     发生变化，或者电机特性改变（例如更换电机），则 JRP 可能需要重新测量或计算 *)
  Parameter JRP : R.

  (** 拉力常数和扭矩常数，单位无，见6.1.3节 *)
  Parameter c_T : R.
  Parameter c_M : R.

  (** 机体中心和任一电机的距离（假定等距），(单位 m) *)
  Parameter d : R.
  Axiom d_gt0 : 0 < d.
  
End Config.

Hint Resolve
  Config.g_gt0
  Config.g_neq0
  Config.m_gt0
  Config.m_neq0
  Config.d_gt0
  : fcs.

(** ** An simplified theory for Propulsion Subsystem *)
(* 
   由于PS内部实现较为复杂，而且有些参数并不需要解析解，相反只通过实验来测定。
   比如拉力常数c_T和扭转常数c_M。如果将PS内部细节完全暴露则加大了验证难度。
   所以，为了简化逻辑，我们以定义的方式引出了PS内部的最主要的结论。
   使用时，函数参数的一致性需要用户保证（当然，这本来就是一个很困难的事情）。
   这些定义的正确性，可利用PSModel和PSExtension中的模式进行再次验证，
   但目前我暂时没有精力做完这些，最主要问题还是PS的内部需要再次优化。
   未来，我们会改进PS的内部设计，以便让外部模块可以使用原始理论，而不是这里的简化。
*)
Module PSTheory.
  (** 由螺旋桨转速角速度 ϖ (rad/s) 计算螺旋桨拉力 T (N) *)
  Definition get_T_by_propAngv (propAngv : R) :=
    Config.c_T * (propAngv * propAngv).

  (** 由螺旋桨转速角速度 ϖ (rad/s) 计算螺旋桨反扭矩 M (N.m) *)
  Definition get_M_by_propAngv (propAngv : R) :=
    Config.c_M * (propAngv * propAngv).
End PSTheory.

Hint Unfold
  PSTheory.get_T_by_propAngv
  PSTheory.get_M_by_propAngv
  : fcs.

