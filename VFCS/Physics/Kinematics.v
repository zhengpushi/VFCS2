(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Kinematics
  author    : Zhengpu Shi
  date      : 2023.04

  reference :
  1. 大学物理
 *)

Require Export VectorRfun.

Open Scope vec_scope.

Notation A := tpRFun.

(** * 1. 质点运动的矢量描述 *)

(** ** 1.1 位移和元位移 *)

Section displacement.
  Context {n : nat}.

  (** P点到Q点的位移，记做 Δr⃗。只与初末时刻两点的位置有关，与轨迹无关。 *)
  Definition displacement (P Q : vec n) := P - Q.

  (** 元位移 dr⃗ 是：当Δt趋于零时，位移的值。即 dr⃗ = lim (Δt→0) r⃗ *)
End displacement.

(** ** 1.2 速度和速率 *)
Section velocity.
  Context {n : nat}.

  (** 平均速度 <v⃗> *)
  Definition velocity_average (P Q : vec n) (delta_t : R) : vec n :=
    let dt := fconst (1/delta_t) in dt c* displacement P Q.

  (** 速度 *)
  Definition velocity (r : vec n) : vec n := 

End velocity.


  Compute displacement.
  Check derive.
  Variable f : A.
  Check f ''.
  Locate "'".
  Check (displacement)'.
  
Check vec.

