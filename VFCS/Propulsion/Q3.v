(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Model of Question 3
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)

Require Import PSExtension.


(** Solve maximum payload and pitch angle: G_maxload, theta_max *)
Section Q3.
  
  Definition the_sigma_e := 0.8.
  Hypothesis arg_sigma_e : is_sigma_e the_sigma_e.
  
  Definition the_U_eo := get_U_eo_by_sigma_e the_sigma_e.
  
  Lemma the_U_eo_ok : is_U_eo the_U_eo.
  Proof.
    fill_params the_U_eo. apply get_U_eo_by_sigma_e_ok. easy.
  Qed.
  
  Definition the_N := get_N_by_U_eo the_U_eo.
  Hypothesis arg_N_gt0 : 0 < the_N.
  
  Lemma the_N_ok : is_N the_N.
  Proof. fill_params the_N. apply get_N_by_U_eo_ok. apply the_U_eo_ok. Qed.
  
  Definition the_T := get_T_by_N the_N.
  
  Lemma the_T_ok : is_T the_T.
  Proof. 
    fill_params the_T. apply get_T_by_N_ok. auto. apply the_N_ok.
  Qed.
  
  Definition the_G_maxload := get_G_maxload the_T.
  
  Lemma the_G_maxload_ok : is_G_maxload the_G_maxload.
  Proof. fill_params the_G_maxload. apply get_G_maxload_ok. apply the_T_ok. Qed.
  
  Definition the_theta_max := get_theta_max the_T.
  
  Lemma the_theta_max_ok : is_theta_max the_theta_max.
  Proof. fill_params the_theta_max. apply get_theta_max_ok. apply the_T_ok. Qed.
  
End Q3.
