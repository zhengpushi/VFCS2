(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Model of Question 2
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)

Require Import PSExtension.


(** Solve system efficiency in the maximum throttole mode *)
Section Q2.
  
  Definition the_sigma_e := 1.0.
  Hypothesis arg_sigma_e : is_sigma_e the_sigma_e.
  
  Definition the_U_eo := get_U_eo_by_sigma_e the_sigma_e.
  
  Lemma the_U_eo_ok : is_U_eo the_U_eo.
  Proof.
    fill_params the_U_eo. apply get_U_eo_by_sigma_e_ok. easy.
  Qed.
  
  Definition the_N := get_N_by_U_eo the_U_eo.
  Hypothesis arg_N_gt0 : 0 < N.
  
  Lemma the_N_ok : is_N the_N.
  Proof. fill_params the_N. apply get_N_by_U_eo_ok. apply the_U_eo_ok. Qed.
  
  Definition the_M := get_M_by_N the_N.
  
  Lemma the_M_ok : is_M the_M.
  Proof. fill_params the_M. apply get_M_by_N_ok.
    rewrite <- the_N_ok;auto. apply the_N_ok. Qed.
  
  Definition the_I_m := get_I_m_by_M the_M.
  
  Lemma the_I_m_ok : is_I_m the_I_m.
  Proof. fill_params the_I_m. apply get_I_m_by_M_ok. apply the_M_ok. Qed.
  
  Definition the_I_e := get_I_e_by_sigma_e_and_I_m the_sigma_e the_I_m.
  
  Lemma the_I_e_ok : is_I_e the_I_e.
  Proof.
    fill_params the_I_e. apply get_I_e_by_sigma_e_and_I_m_ok; auto.
    apply the_I_m_ok.
  Qed.
  
  Definition the_I_b := get_I_b_by_I_e the_I_e.
  
  Lemma the_I_b_ok : is_I_b the_I_b.
  Proof. fill_params the_I_b. apply get_I_b_by_I_e_ok. apply the_I_e_ok. Qed.
  
  Definition the_eta := get_eta_by_M_and_N_and_I_b the_M the_N the_I_b.
  
  Lemma the_eta_ok : is_eta the_eta.
  Proof.
    fill_params the_eta. apply get_eta_by_M_and_N_and_I_b_ok.
    apply the_M_ok. apply the_N_ok. apply the_I_b_ok.
  Qed.

End Q2.
