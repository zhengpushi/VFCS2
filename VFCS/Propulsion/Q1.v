(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Model of Question 1
  author    : Zhengpu Shi
  date      : 2021.05.25
  
  reference:
  1. 多旋翼飞行器设计与控制，全权
*)

Require Import PSExtension.


(** Solve maximum hovering time *)
Section Q1.
  
  Definition the_State := Hovering.
  
  Hypothesis arg_State : is_State the_State.
  
  (* 4.24 *)
  Definition the_T := (* the_G / the_n_r *) G / n_r.
  
  Lemma the_T_ok : is_T the_T.
  Proof. 
    fill_params the_T. rewrite Hovering_Balance; auto. field. neq0.
  Qed.
  
  Lemma the_T_gt0 : 0 < the_T.
  Proof.
    autounfold with fcs in *. compute. subst. gt0.
  Qed.
  
  Hint Resolve the_T_gt0 : fcs.
  
  (** 4.25 *)
  
  Definition the_N := get_N_by_T the_T.
  
  Hypothesis arg_N : is_N the_N.
  Hypothesis arg_N_gt0 : 0 < N.
  
  Lemma the_N_ok : is_N the_N.
  Proof.
    fill_params the_N.
    rewrite (get_N_by_T_ok the_T); auto. apply the_T_ok.
  Qed.
  
  Definition the_M := get_M_by_N the_N.
  
  Lemma the_M_ok : is_M the_M.
  Proof. fill_params the_M. rewrite (get_M_by_N_ok the_N); auto.
    rewrite <- arg_N. auto. Qed.
  
  (* Notice that, even the_M2 could be prove, but it is a wrong program!
    because, if the_N is different with N, the result will different! *)
  Definition the_M2 := get_M_by_N N.
  Lemma the_M2_ok : is_M the_M2.
  Proof. 
    fill_params the_M2. rewrite (get_M_by_N_ok the_N); auto. f_equal. auto.
    rewrite <- arg_N; auto.
  Qed.
  
  (** 4.26 *)
  
  Definition the_U_m := get_U_m_by_M_and_N the_M the_N.
  
  Lemma the_U_m_ok : is_U_m the_U_m.
  Proof.
    fill_params the_U_m. apply get_U_m_by_M_and_N_ok; auto. apply the_M_ok.
  Qed.
  
  Definition the_I_m := get_I_m_by_M the_M.
  
  Lemma the_I_m_ok : is_I_m the_I_m.
  Proof.
    fill_params the_I_m.  apply get_I_m_by_M_ok. apply the_M_ok.
  Qed.
  
  (** 4.27 (1),(2) *)
  
  Definition the_sigma_e := get_sigma_e_by_U_m_and_I_m the_U_m the_I_m.
  
  Lemma the_sigma_e_ok : is_sigma_e the_sigma_e.
  Proof.
    fill_params the_sigma_e.
    apply get_sigma_e_by_U_m_and_I_m_ok; auto.
    apply the_U_m_ok. apply the_I_m_ok.
  Qed.
  
  Definition the_I_e := get_I_e_by_sigma_e_and_I_m the_sigma_e the_I_m.
  
  Lemma the_I_e_ok : is_I_e the_I_e.
  Proof.
    fill_params the_I_e.
    apply get_I_e_by_sigma_e_and_I_m_ok; auto.
    apply the_sigma_e_ok. apply the_I_m_ok.
  Qed.
  
  (** 4.28 *)
  Definition the_I_b := get_I_b_by_I_e the_I_e.
  
  Lemma the_I_b_ok : is_I_b the_I_b.
  Proof.
    fill_params the_I_b. apply get_I_b_by_I_e_ok. apply the_I_e_ok.
  Qed.
  
  (** 4.27 (3) *)
  Definition the_U_e := get_U_e_by_I_b the_I_b.
  
  Lemma the_U_e_ok : is_U_e the_U_e.
  Proof.
    fill_params the_U_e. apply get_U_e_by_I_b_ok; auto. apply the_I_b_ok.
  Qed.
  
  (** 4.29 *)
  Definition T_hover := get_T_b_by_I_b the_I_b.
  
  Lemma T_hover_ok : is_T_b T_hover.
  Proof.
    fill_params T_hover. apply get_T_b_by_I_b_ok; auto. apply the_I_b_ok.
  Qed.

End Q1.
