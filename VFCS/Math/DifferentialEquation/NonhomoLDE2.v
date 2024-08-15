(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2nd-order non-homogeneous linear differential equation
              二阶常系数非齐次线性微分方程
  author    : Zhengpu Shi
  date      : 2024.05
 *)

Require Import DEbase.


(* ######################################################################### *)
(** * General solution of 2nd-order non-homogeneouse linear differential equation *)
  
Definition second_order_non_ode (a b c : R) (y : R -> R) (f : R -> R) :=
  forall t : R,
    let dy := Derive y in
    a * (Derive dy t) + b * (Derive y t) + c * y t = f t.

