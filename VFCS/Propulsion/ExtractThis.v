(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extract code from Coq to OCaml, include all files
  author    : Zhengpu Shi
  date      : 2020.11.17
*)

Require Import PSExtension Q1 Q2 Q3 Q4.
Require Import Extraction.


(** Give some conversion rules manually *)

(* the command provided by std library will generate warning *)
(* Require Import extraction.ExtrOcamlBasic.
Require Import extraction.ExtrOcamlNatInt.
Require Import extraction.ExtrOcamlZInt. *)
 

(* some inductive datatypes *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "Int.succ" ] 
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* constant - Real number and operations *)
Extract Constant R => float.

(* patch for coq 8.11 and newer *)
Extract Constant Rabst => "__".
Extract Constant Rrepr => "__".

Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant PI => "Float.pi".
Extract Constant Rplus => "(+.)".
Extract Constant Rmult => "( *. )".
Extract Constant Rminus => "(-.)".
Extract Constant Ropp => "fun a -> (0.0 -. a)".
Extract Constant Rinv => "fun a -> (1.0 /. a)".
Extract Constant Rpower => "Float.pow".
Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant atan => "Float.atan".
Extract Constant acos => "Float.acos".
(* Extract Constant pow => 
  "fun r0 n -> if n=0 then 1.0 else (r0 *. (pow r0 (n-1)))". *)

Extraction Inline 
  C_d C_fd  H_p D_p K0 e A epsilon alpha0.

Extract Constant P_a0 => "val_P_a0".
Extract Constant T0 => "val_T0".
Extract Constant e => "val_e".
Extract Constant rho0 => "val_rho0".
Extract Constant h => "val_h".
Extract Constant T_t => "val_T_t".
Extract Constant n_r => "val_n_r".
Extract Constant G => "val_G".
Extract Constant I_other => "val_I_other".
Extract Constant D_p => "val_D_p".
Extract Constant G => "val_G".
Extract Constant H_p => "val_H_p".
Extract Constant B_p => "val_B_p".
Extract Constant A => "val_A".
Extract Constant epsilon => "val_epsilon".
Extract Constant lambda => "val_lambda".
Extract Constant zeta => "val_zeta".
Extract Constant e => "val_e".
Extract Constant K0 => "val_K0".
Extract Constant alpha0 => "val_alpha_0".
Extract Constant C_fd => "val_C_fd".
Extract Constant K_V0 => "val_K_V0".
Extract Constant I_mMax => "val_I_mMax".
Extract Constant U_m0 => "val_U_m0".
Extract Constant I_m0 => "val_I_m0".
Extract Constant R_m => "val_R_m".
Extract Constant G_m => "val_G_m".
Extract Constant I_eMax => "val_I_eMax".
Extract Constant R_e => "val_R_e".
Extract Constant G_e => "val_G_e".
Extract Constant C_b => "val_C_b".
Extract Constant C_min => "val_C_min".
Extract Constant K_b => "val_K_b".
Extract Constant R_b => "val_R_b".
Extract Constant U_b => "val_U_b".
Extract Constant C_D1 => "val_C_D1".
Extract Constant C_D2 => "val_C_D2".
Extract Constant S => "val_S".

Extract Constant val_0_0065 => "0.0065".
Extract Constant val_5_2561 => "5.2561".
Extract Constant val_9_55 => "9.55".
Extract Constant val_0_06 => " 0.06". 

(* Extraction C_d. *)
(* let C_d =
  let r1 =
    rdiv (rminus (rmult epsilon (atan (rdiv h_p (rmult pI d_p)))) alpha0)
      (rplus (rmult pI a) k0)
  in
  rplus c_fd (rmult (rdiv (rmult (rmult pI a) (rsqr k0)) e) (rsqr r1)) *)
  
(* Recursive Extraction  *)
(*   C_d C_T C_M get_G_maxload_by_T get_T_by_N . *)

(*
Extraction "PS.ml"
  C_d C_T C_M get_G_maxload_by_T get_T_by_N .
  
Extraction "PS.ml"
  C_d C_T C_M K_E K_T get_G_maxload_by_T get_T_by_N 
  get_M_by_N 
  get_N_by_T 
  get_N_by_M 
  get_T_by_M 
  get_M_by_T 
  get_I_b_by_I_e 
  get_T_b_by_I_b 
  get_I_m_by_M 
  get_I_m_by_M_direct 
  get_I_m_by_T 
  get_I_m_by_N 
  get_U_m_by_M_and_N 
  get_M_by_I_m 
  get_E_a_by_N 
  get_E_a_by_T 
  get_E_a_by_M 
  get_U_m_by_E_a_and_I_m 
  get_U_m_by_N_and_M 
  get_U_m_by_N 
  get_U_m_by_M 
  get_U_m_by_T 
  get_U_eo_by_U_m_and_I_m 
  get_U_eo_by_sigma_e 
  get_U_eo_by_E_a_and_I_m 
  get_U_eo_by_N 
  get_I_e_by_sigma_e_and_I_m 
  get_U_e_by_I_b 
  get_eta_by_M_and_N_and_I_b 
  get_sigma_e_by_U_m_and_I_m 
  get_sigma_e_by_E_a_and_I_m 
  get_I_e_by_E_a_and_I_m 
  get_I_e_by_T 
  get_U_e_by_I_e 
  get_T_b_by_I_e 
  get_N_by_U_m 
  get_N_by_U_eo .

Extraction "Q1.ml"
  Q1.the_State 
  Q1.the_T 
  Q1.the_N 
  Q1.the_M 
  Q1.the_U_m 
  Q1.the_I_m 
  Q1.the_sigma_e 
  Q1.the_I_e 
  Q1.the_I_b 
  Q1.the_U_e 
  Q1.T_hover .

(* Print Q2. *)
Extraction "Q2.ml"
  Q2.the_sigma_e 
  Q2.the_U_eo 
  Q2.the_N 
  Q2.the_M 
  Q2.the_I_m 
  Q2.the_I_e 
  Q2.the_I_b 
  Q2.the_eta.

Extraction "Q3.ml"
  Q3.the_sigma_e
  Q3.the_U_eo
  Q3.the_N
  Q3.the_T
  Q3.the_G_maxload
  Q3.the_theta_max.

Extraction "Q4.ml"
  Q4.the_State 
  Q4.the_V 
  Q4.the_N 
  Q4.the_M 
  Q4.the_U_m 
  Q4.the_I_m 
  Q4.the_sigma_e 
  Q4.the_I_e 
  Q4.the_I_b 
  Q4.the_T_b 
  Q4.the_Z .

*)
