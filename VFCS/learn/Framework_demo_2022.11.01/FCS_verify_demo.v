
(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


  如何表示牛顿运动定律、动能定理、动量定理等？
忽然有的想法。Record结构体 + Relation定义规范，然后定义funciton后，
再验证其满足规范。*)

Require Import Reals.
Open Scope R.

Notation Real := R.

(** 质量、加速度、力，三者形成的一个结构体，
    作用：命名各个分量，方便管理。*)
Record MassAccForce := {
    Mass : Real;
    Acc : Real;
    Force : Real
  }.

(** 定义规范 *)
Definition MAF_spec (maf: MassAccForce) : Prop :=
  let (m,a,f) := maf in m * a = f.

(** 定义一个函数，表示 m = f / acc *)
Definition get_mass_by_acc_force (acc force : R) : R :=
  force / acc.

(** 验证且满足规范 *)
Lemma get_mass_by_acc_force_spec : forall acc force,
    acc <> 0 ->
    let mass := get_mass_by_acc_force acc force in
    let maf := Build_MassAccForce mass acc force in
    MAF_spec maf.
Proof.
  intros. cbv. field. auto.
Qed.

(** 有一定的效果，但是 spec 如果写错了，比如 acc,mass,force 都是 R 类型，
    如果不小心调换了顺序，那么验证也许是错的。
    一个复杂的思路是，写更复杂的类型系统，但暂时不必大动干戈。
    但是，spec的正确性一直是痛点，目前都用人工检查的方式。
    一个更重要的问题是，找出的边界条件，acc≠0，如何发挥作用？
    另外，如何大规模的编写这种设计和规范？
 *)
