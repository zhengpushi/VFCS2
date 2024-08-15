(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Multicopter Aerodynamic Drag Model 多旋翼气动阻力模型
  author    : Zhengpu Shi
  date      : Jun, 2024

  reference : 
  1. Introduction to Multicopter Design and Control, QuanQuan, 2017

 *)

Require Export PS.
Require Export AttitudeRepr.
Require Export ControlModel.

Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * 气动阻力模型 *)

