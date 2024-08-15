Require Import Reals.
Require Import List.
Import ListNotations.

Require Import Matrix.Mat_def.
Require Import Matrix.Mat_trans.
Require Import Matrix.Mat_trans_lemma.
Require Import Matrix.Matrix_Module.
Require Import Matrix.FMatrix.
Require Import Matrix.RSupport.

(*矩阵和向量维度*)
Variable n m: nat.


(* xk是k时刻的状态向量
xk1 是k-1时刻的状态向量 
uk1是k-1时刻的控制向量 
wk1是k-1时刻的系统噪声*)
(* Variable xk: @Mat (R->R) n 1. *)
Variable  xk1 uk1 wk1: FMat n 1.

(*zk是k时刻的观测向量  
 vk是k时刻的观测噪声*)
Variables  vk:FMat m 1.

(*phik1是k-1时刻到k时刻的系统转移矩阵 是不变的常数矩阵
gammak1是系统噪声矩阵 表征各噪声分别影响个状态的程度
Hk是k时刻的观测矩阵*)
Variable phik1 gammak1: FMat n n. 
Variables Hk : FMat m n.
(**连续时间线性系统**)
Section Chap8_2_3_Discrete_time_linear_system.


(*离散时间线性系统模型 8.38*)
(* xk = Φ *xk1 + uk1 + Γ*wk1 *)
(* zk = H *xk + vk*)
(* 
Axiom Discrete_time_linear_system_xk : xk FM= (phik1 FM* xk1) FM+ uk1 FM+ (gammak1 FM* wk1).
Axiom Discrete_time_linear_system_zk : zk FM= (Hk FM* xk) FM+ vk. 
 *)
(* xk是k时刻的状态向量 *)
Definition xk := (phik1 FM* xk1) FM+ uk1 FM+ (gammak1 FM* wk1).
Definition zk := (Hk FM* xk) FM+ vk. 
End Chap8_2_3_Discrete_time_linear_system.

Section Kalman_filtering.
(* Exkk是k时刻状态的最小方差无偏估计  ESxkk1 是在上一时刻状态估计ESxk1k1 的基础上对当前时刻状态xk的一步预测 8.5.7*)
(* Variable ESxkk : @Mat (R->R) n 1. *)
(* Variable ESxkk1 : @Mat (R->R) n 1. *)
Variable ESxk1k1 : FMat n 1.

(*----------------------------8.57-----------------------------*)
(*  ESxkk1 = phi*ESxk1k1 + u                                   *)
(*  ESzkk1 = H*ESxk1k1                                         *)
(*  ESxkk1 是在上一时刻状态估计ESxk1k1 的基础上对当前时刻状态xk的一步预测*)
(*  ESzkk1 是在ESxkk1的基础上对当前时刻zk的一步预测                  *)
(*-------------------------------------------------------------*)
Definition ESxkk1 := phik1 FM* ESxk1k1 FM+ uk1.
Definition ESzkk1 := Hk FM* ESxkk1.

Variable Kk' Kk'': FMat n n. 
Variable Kk: FMat n m.


Definition In:= FMI n .

(*由于是线性估计器，估计EXxkk(estimate x_(k|k))可以表示未先验估计和观测值的线性组合形式  8.45
ESxkk = Kk' * Exk1k1 + Kkzk + Kk'' * uk1   *)
Definition ESxkk := Kk' FM* ESxk1k1 FM+ Kk FM* zk FM+ Kk'' FM* uk1.

(*------------------------*)
(* 2 参数Kk' 和 Kk''的推导  *)
(*------------------------*) 
(**ERxkk为状态误差 8.47 **)
(**ERxkk = xk - ESxkk **)
(* Axiom ERxkk_847 :ERxkk FM=  xk FM- ESxkk.
Axiom ERxk1k1_847 :ERxk1k1 FM=  xk1 FM- ESxk1k1.
Axiom ERxkk1_847 :ERxkk1 FM=  xk FM- ESxkk1. *)
Definition ERxkk :=  xk FM- ESxkk.
Definition ERxk1k1 :=  xk1 FM- ESxk1k1.
Definition ERxkk1 :=  xk FM- ESxkk1.

(*ESxkk 是xkk的无偏估计，则误差ERxkk=0 (Error x_(k|k))    8.46*)
(*    8.46       *)
Axiom ERxkk_eq0 : ERxkk FM= FMO n 1.
Axiom ERxk1k1_eq0 : ERxk1k1 FM= FMO n 1. 

Lemma error_x_kk_848 : ERxkk FM= xk FM- (Kk' FM* ESxk1k1 FM+ Kk FM* zk FM+ Kk'' FM* uk1).
Proof.
  reflexivity.
Qed.



(*-----------3.1 8.49---------------*)
Lemma error_xkk_3_1: ERxkk FM= 
phik1 FM* xk1 FM+ uk1 FM+ gammak1 FM* wk1 FM- 
Kk' FM* ESxk1k1 FM- 
Kk FM* (Hk FM* (phik1 FM* xk1 FM+ uk1 FM+ (gammak1 FM* wk1)) FM+ vk) FM- 
Kk'' FM* uk1.
Proof.
  unfold ERxkk.
  unfold ESxkk.
  unfold zk.
  unfold xk.
  rewrite <- ?FMsub_assoc.
  reflexivity.
Qed.


(*----------------------------3.2  8.50---------------------------------*)
(* ER = (phi-KHphi)xk1 - K'ES + (gamma-KHgamma)w + (I-KH-K'')u - Kv *)
Lemma error_xkk_3_2: ERxkk FM=
(phik1 FM- Kk FM* Hk FM* phik1) FM* xk1 FM-
Kk' FM* ESxk1k1 FM+
(gammak1 FM- Kk FM* Hk FM* gammak1) FM* wk1 FM+
(In FM- Kk FM* Hk FM- Kk'' ) FM* uk1 FM- 
Kk FM* vk.
Proof.
  rewrite error_xkk_3_1.
  rewrite ?FMmul_sub_distr_l.
  rewrite ?FMmul_add_distr_r.
  rewrite <- ?FMmul_assoc.
  rewrite <- ?FMsub_assoc. 
  rewrite <- ?FMadd_assoc1.
  rewrite FMmul_unit_l.
  unfold FMsub.
  rewrite FMsub_comm1 .
  apply Fmat_sub_compat. 2: { reflexivity. }
  apply Fmat_sub_compat. 2: { reflexivity. }
  rewrite FMsub_comm1 .
  apply Fmat_sub_compat. 2: { reflexivity. }
  rewrite <- FMadd_comm1.
  apply Fmat_sub_compat. 2: { reflexivity. }
  rewrite FMsub_comm1 .
  repeat rewrite <- FMadd_comm1.
  rewrite FMadd_comm2. 
  reflexivity.
Qed.

(*------------------------4.22----8.51-------------------------------------------*)
(* ER = (phi-KHphi-K')xk1 + K'(xk1-ES) + (gamma-KHgamma)w + (I-KH-K'')u - Kv *)
Lemma error_xkk_4_22: ERxkk FM=
(phik1 FM- Kk FM* Hk FM* phik1 FM- Kk') FM* xk1 FM+
Kk' FM* (xk1 FM- ESxk1k1) FM+
(gammak1 FM- Kk FM* Hk FM* gammak1) FM* wk1 FM+
(In FM- Kk FM* Hk FM- Kk'' ) FM* uk1 FM- 
Kk FM* vk.
Proof.
  rewrite error_xkk_3_2.
  apply mat_sub_compat'. 2: { reflexivity. }
  repeat apply mat_add_compat';try reflexivity.
  rewrite ?FMmul_sub_distr_l.
  rewrite ?FMmul_sub_distr_r.
  rewrite <- FMadd_assoc1.
  rewrite <- FMadd_comm1.
  rewrite FMadd_assoc1.
  rewrite FMsub_self.
  rewrite FMadd_zero_r.
  reflexivity.
Qed.

Lemma error_x_kk_852: ERxkk FM=
(phik1 FM- Kk FM* Hk FM* phik1 FM- Kk') FM* xk1 FM+
(In FM- Kk FM* Hk FM- Kk'' ) FM* uk1 FM+
Kk' FM* (xk1 FM- ESxk1k1) FM+
(gammak1 FM- Kk FM* Hk FM* gammak1) FM* wk1  FM- 
Kk FM* vk.
Proof.
  rewrite error_xkk_4_22.
  rewrite FMadd_comm2.
  apply mat_sub_compat'. 2: { reflexivity. }
  apply mat_add_compat'. 2: { reflexivity. }
  rewrite FMadd_comm2.
  reflexivity.
Qed.

(*卡尔曼滤波器要求wk和vk是互不相关的零均值高斯白噪声序列，即 vk=0 wk=0 8.39*)
Axiom v_eq0:  vk FM= FMO m 1.
Axiom w_eq0: wk1 FM= FMO n 1.

(*-----------------------4.23-----8.53---------------------------------------*)
(*  (phi-KHphi-K')xk1 + (I-KH-K'')u=0                                        *)
(*---------------------------------------------------------------------------*)
Lemma eq0_423: (phik1 FM- Kk FM* Hk FM* phik1 FM- Kk') FM* xk1 FM+ (In FM- Kk FM* Hk FM- Kk'' ) FM* uk1 FM= FMO n 1.
Proof.
  rewrite <- ERxkk_eq0.
  rewrite error_x_kk_852.
  assert(ERxk1k1 FM= xk1 FM- ESxk1k1). {reflexivity. }
  rewrite <- H.
  rewrite v_eq0,w_eq0,ERxk1k1_eq0.
  rewrite ?FMmul_zero_l.
  rewrite FMsub_zero_r.
  rewrite ?FMadd_zero_r.
  reflexivity.
Qed.


(*xk1 和 uk1 分别为系统的状态向量和控制向量，不能时刻为0 *)
Axiom noteq0_xk1 : not(xk1 FM= FMO n 1).
Axiom noteq0_uk1 : not(uk1 FM= FMO n 1).

(*  A*B + C*D = 0 .B D不等于0 ->  A C 等于0*)
Axiom eq0:forall {n m p:nat} (A C:@Mat (R->R) m n) (B D:@Mat (R->R) n p) ,
A FM* B FM+ C FM* D FM= FMO  m p ->
not(B FM= FMO n p) -> not(D FM= FMO  n p) -> A FM= FMO m n /\ C FM= FMO m n.

(*----------------------------8.54-------------------*)
(*  (phi-KHphi-K')xk1 =0                             *)
(*  (I-KH-K'')u=0                                    *)
(*---------------------------------------------------*)

Lemma eq0_854_1:  phik1 FM- Kk FM* Hk FM* phik1 FM- Kk' FM= FMO n n.
Proof.
apply (eq0  (phik1 FM- Kk FM* Hk FM* phik1 FM- Kk')  (In FM- Kk FM* Hk FM- Kk'') xk1 uk1).
apply eq0_423. apply noteq0_xk1. apply noteq0_uk1.
Qed.

Lemma eq0_854_2: In FM- Kk FM* Hk FM- Kk'' FM= FMO n n.
apply (eq0  (phik1 FM- Kk FM* Hk FM* phik1 FM- Kk')  (In FM- Kk FM* Hk FM- Kk'') xk1 uk1).
apply eq0_423. apply noteq0_xk1. apply noteq0_uk1.
Qed.


(*----------------------------8.55-------------------*)
(*  K'=phi-KHphi                                     *)
(*  K''=I-KH                                         *)
(*---------------------------------------------------*)
Lemma Kk'_4_5: Kk' FM= phik1 FM- Kk FM* Hk FM* phik1.
Proof.
  assert(phik1 FM- Kk FM* Hk FM* phik1 FM- Kk' FM+ Kk' FM= FMO n n FM+ Kk').
    { 
    apply mat_add_compat'. 
    apply eq0_854_1. reflexivity. 
    }
  rewrite FMadd_zero_l in H.
  rewrite <- FMadd_comm1 in H.
  rewrite FMadd_assoc1 in H.
  rewrite FMsub_self in H.
  rewrite FMadd_zero_r in H.
  symmetry.
  apply H.
Qed.
  
Lemma Kk''_4_5:  Kk'' FM= In FM- Kk FM* Hk.
Proof.
  assert(In FM- Kk FM* Hk FM- Kk''  FM+ Kk''  FM= FMO n n FM+ Kk'').
  { 
  apply mat_add_compat'. apply eq0_854_2. reflexivity. 
  }
  rewrite FMadd_zero_l in H.
  rewrite <- FMadd_comm1 in H.
  rewrite FMadd_assoc1 in H.
  rewrite FMsub_self in H.
  rewrite FMadd_zero_r in H.
  symmetry.
  apply H.
Qed.

(*-----------------4.26-------8.56-------------------*)
(* ESxkk = ESxkk1 + K(z - ESzkk1)                    *)
(*---------------------------------------------------*)

Lemma estimate_xkk_4_26: ESxkk FM= ESxkk1 FM+ Kk FM*(zk FM- ESzkk1).
Proof.
  unfold ESxkk.
  rewrite Kk'_4_5,Kk''_4_5.
  unfold ESxkk1,ESzkk1,ESxkk1.
  rewrite ?FMmul_sub_distr_l.
  rewrite ?FMmul_sub_distr_r.
  rewrite ?FMmul_add_distr_r.
  rewrite <- ?FMmul_assoc.
  rewrite FMmul_unit_l.
  rewrite <- FMsub_assoc.
  rewrite <- ?FMadd_assoc1.
  apply mat_sub_compat'. 2: { reflexivity. }
  rewrite FMadd_comm2.
  rewrite FMadd_comm1.
  apply mat_add_compat'. 2: { reflexivity. }
  symmetry.
  apply FMadd_comm1.
Qed.

(*-------------------*)
(* 3 参数Kk的推导      *)
(*-------------------*) 

Definition Pkk := ERxkk FM* T(ERxkk).
Definition Pkk1 := ERxkk1 FM* T(ERxkk1).
Definition Rk := vk FM* T(vk).

(*----------------4.31--------8.59-------------------*)
(* ERxkk = (I-KH)ERxkk1 - Kv                         *)
(*---------------------------------------------------*)

Lemma error_xkk_4_31: ERxkk FM= (In FM- Kk FM* Hk) FM* ERxkk1 FM- Kk FM* vk.
Proof.
  unfold ERxkk.
  rewrite estimate_xkk_4_26.
  unfold ESzkk1.
  rewrite <- FMsub_assoc. 
  unfold zk.
  rewrite FMadd_comm1.
  rewrite FMmul_add_distr_r.
  rewrite FMmul_sub_distr_r.
  rewrite <- ?FMmul_assoc.
  rewrite <- FMsub_assoc.
  rewrite FMmul_sub_distr_l.
  rewrite FMmul_unit_l.
  unfold ERxkk1.
  rewrite FMmul_sub_distr_r.
  reflexivity.
Qed.

(*----------------------------8.60------------------------*)
(* ERxkk * T_ERxkk = (I-KH) * ERxkk1 * T_ERxkk * T_(I-KH) *)         
(*                 - (I-KH)ERxkk1 * T_v * T_K             *)
(*                 - K * v * T_ERxkk*T_(I-KH)             *)
(*                 + K * v * T_v * T_K                    *)
(*--------------------------------------------------------*)
Lemma ERxkk_mul_T_ERxkk_860: ERxkk FM* T(ERxkk) FM= 
(In FM- Kk FM* Hk) FM* ERxkk1 FM* T(ERxkk1) FM* T(In FM- Kk FM* Hk) 
FM- (In FM- Kk FM* Hk) FM* ERxkk1 FM* T(vk) FM* T(Kk) 
FM- Kk FM* vk FM* T(ERxkk1) FM* T(In FM- Kk FM* Hk) 
FM+ Kk FM* vk FM* T(vk) FM* T(Kk).
Proof.
  assert(T(ERxkk) FM=  T(ERxkk1) FM* T(In FM- Kk FM* Hk)  FM- T(vk) FM* T(Kk)).
  {
  rewrite error_xkk_4_31.
  rewrite FMteq_sub.
  rewrite ?FMteq_mul.
  reflexivity.
  }
  rewrite H.
  rewrite error_xkk_4_31.
  rewrite ?FMmul_sub_distr_r.
  rewrite ?FMmul_sub_distr_l.
  rewrite <- FMsub_assoc1.
  rewrite FMsub_comm1.
  rewrite <- ?FMmul_assoc.
  reflexivity.
Qed.
  
 (*----------------------------8.61------------------*)
(* ERxkk 与噪声vk 无关                                *)
(* ERxkk * T_v = 0                                   *)
(* v * T_ERxkk =0                                    *)
(*---------------------------------------------------*)

Axiom ERxkk1_Tv_eq0:ERxkk1 FM* T(vk) FM= FMO n m.
Axiom v_TERxkk1_eq0:vk FM* T(ERxkk1) FM= FMO m n.

(*----------------4.33--------8.62------------------------*)
(* Pkk = (I-KH) * Pkk1 * T_(I-KH)                         *)         
(*                 + K * R * T_K                          *)
(*--------------------------------------------------------*)
Lemma Pkk_4_33: Pkk FM= (In FM- Kk FM* Hk) FM* Pkk1 FM* T(In FM- Kk FM* Hk)  FM+ Kk FM* Rk FM* T(Kk).
Proof.
  unfold Pkk,Pkk1,Rk.
  rewrite ERxkk_mul_T_ERxkk_860.
  rewrite  FMmul_assoc with(middle:=ERxkk1)(right:=T( vk)).
  rewrite  FMmul_assoc with(middle:=vk)(right:=T( ERxkk1)).
  rewrite ERxkk1_Tv_eq0,v_TERxkk1_eq0.
  rewrite ?FMmul_zero_l.
  rewrite ?FMmul_zero_r.
  rewrite ?FMsub_zero_r.
  rewrite ?FMmul_assoc.
  reflexivity.
Qed.

Definition Pk1k1 := ERxk1k1 FM* T(ERxk1k1).
Definition Qk1 := wk1 FM* T(wk1).


(*----------------------------8.67------------------------------------------------------*)
(*Pkk = Pkk1 - Pkk1 * T(H) * T(K) - K * H * Pkk1 + K *(H * Pkk1 * T(H) + R) * T(K)      *)
(*--------------------------------------------------------------------------------------*)
Lemma Pkk_867: Pkk FM= Pkk1 FM- 
Pkk1 FM* T(Hk) FM* T(Kk) FM- 
Kk FM* Hk FM* Pkk1 FM+ 
Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk) FM* T(Kk).
Proof.
rewrite Pkk_4_33.
  assert(T(In FM- Kk FM* Hk) FM= In FM- T(Hk) FM* T(Kk)).
  {
  rewrite FMteq_sub.
  rewrite FMteq_mul.
  apply mat_sub_compat'. 2: { reflexivity. }
  unfold In.
  unfold FMI. 
  unfold FMatrix.MMI. 
  apply trans_MI.
  }
  rewrite H.
  rewrite ?FMmul_add_distr_r.
  rewrite ?FMmul_add_distr_l.
  rewrite ?FMmul_sub_distr_r.
  rewrite ?FMmul_sub_distr_l.
  rewrite <- ?FMmul_assoc.
  rewrite ?FMmul_unit_l.
  rewrite ?FMmul_unit_r.
  rewrite <- FMsub_assoc1.
  rewrite FMsub_comm1.
  rewrite FMadd_assoc.
  reflexivity.
Qed.


(*tr(Pkk) = tr(Pkk1) - tr(P*T_H*T_K) - tr(KHP) + tr(K(HPT_H)T_K) *)
Lemma tr_Pkk_867: Tr(Pkk)  = Tr(Pkk1) -f 
Tr(Pkk1 FM* T(Hk) FM* T(Kk))  -f
Tr(Kk FM* Hk FM* Pkk1)  +f
Tr(Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk) FM* T(Kk)) .
Proof.
assert(Tr(Pkk) = Tr(Pkk1 FM- Pkk1 FM* T(Hk) FM* T(Kk) FM- 
Kk FM* Hk FM* Pkk1 FM+ 
Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk) FM* T(Kk))).
{ apply FMat_tr_compat.  apply Pkk_867. }
rewrite H.
rewrite FMat_tr_add.
rewrite ?FMat_tr_sub.
reflexivity.
Qed.

(* tr P*T_H*T_K = tr KHP*)
Lemma tr_KHP_eq: Tr(Pkk1 FM* T(Hk) FM* T(Kk)) = Tr(Kk FM* Hk FM* Pkk1) .
Proof.
  assert(Pkk1 FM* T( Hk) FM* T( Kk) FM= T(Kk FM* Hk FM* Pkk1)).
  {
  rewrite ?FMteq_mul. 
  unfold Pkk1.
  rewrite FMteq_mul.
  rewrite FMtteq.
  rewrite <-FMmul_assoc.
  reflexivity.
  }
  unfold FMtr.
  rewrite FMat_tr_trans with (Kk FM* Hk FM* Pkk1).
  apply FMat_tr_compat.
  apply H.
Qed.


(*tr(Pkk) = tr(Pkk1) -2* tr(KHP) + tr(K(HPT_H)T_K) *)
Lemma tr_Pkk_867_1 :Tr(Pkk)  = Tr(Pkk1) -f 
kmul 2 (Tr(Kk FM* Hk FM* Pkk1)) +f
Tr(Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk) FM* T(Kk)) .
Proof.
  rewrite tr_Pkk_867.
  rewrite tr_KHP_eq.
  unfold kmul .
  rewrite fun_minus_assoc.
  reflexivity.
Qed.

(*Deri(tr(Pkk))/Deri Kk = 2K(HPT(H)+R) -2*T(P)T(H)  *)
Lemma Deri_Pkk_867: Deri ( Tr(Pkk) ) Kk FM= 
FMtwoMat (Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk)) FM- 
FMtwoMat (T(Pkk1) FM* T(Hk)).
Proof.
  rewrite FMat_Deri_compat with (mx':= (Pkk1 FM- Pkk1 FM* T(Hk) FM* T(Kk) FM- 
  Kk FM* Hk FM* Pkk1 FM+ Kk FM* ( Hk FM* Pkk1 FM* T(Hk) FM+ Rk) FM* T(Kk))).
  2:{ apply Pkk_867. }
  rewrite ?FMat_Deri_add.
  rewrite ?FMat_Deri_sub.
  rewrite FMat_Deri_not_correlation.
  rewrite FMat_Deri_compat' with (x':=Tr(Kk FM* Hk FM* Pkk1)). 
  2:{ apply tr_KHP_eq. }
  rewrite FMat_Deri_compat with (mx':= Kk FM* (Hk FM* Pkk1)).
  rewrite FMat_Deri_mul.
  2:{ apply FMmul_assoc. }
  rewrite FMat_Deri_trans_eq.
  2:{ 
  unfold Rk.
  unfold Pkk1.
  rewrite FMteq_add.
  rewrite ?FMteq_mul.
  rewrite ?FMtteq.
  rewrite <-FMmul_assoc.
  reflexivity.
  }
  rewrite FMat_Deri_compat with (mx':= Kk FM* (Hk FM* Pkk1)).
  2:{ apply FMmul_assoc. }
  rewrite FMat_Deri_mul.
  rewrite ?FMteq_mul.
  rewrite FMadd_comm.
  rewrite <- ?FMadd_assoc1.
  rewrite FMadd_zero_r.
  unfold FMtwoMat.
  unfold FMatrix.twoMat.
  unfold twoMat.
  rewrite <- FMsub_assoc.
  reflexivity.
Qed.




End Kalman_filtering.

Require Import Matrix.inv.


Section KF_implement.

Definition FMn1 := FMat n 1. (*x u w*)
Definition FMm1 := FMat m 1. (*v *)
Definition FMnn := FMat n n. (*phi gamma *)
Definition FMmn := FMat m n. (*H*)
Definition FMOn1 := FMO n 1.
Definition FMOm1 := FMO m 1.
Definition FMOnn := FMO n n.
Definition FMOmn := FMO m n.
Definition FMIn := FMI n.

Parameter inv : forall {n m :nat}, @Mat (R->R) n m->@Mat (R->R) m n.

Fixpoint KF_k (k:nat) (u_l w_l: list FMn1) (v_l z_l: list FMm1) (phi_l gamma_l: list FMnn)
(H_l: list FMmn) (x0: FMn1) (P0: FMnn):= 
match k with
|O => (x0,P0)
|S n => let x' := fst (KF_k n u_l w_l v_l z_l phi_l gamma_l H_l x0 P0) in
        let P' := snd (KF_k n u_l w_l v_l z_l phi_l gamma_l H_l x0 P0) in
        let phi := nth n phi_l FMOnn in 
        let u := nth n u_l FMOn1 in 
        let gamma := nth n gamma_l FMOnn  in
        let w := nth n w_l FMOn1 in
        let H := nth (S n) H_l FMOmn in
        let v := nth (S n) v_l FMOm1 in
        let z := nth (S n) z_l FMOm1 in
        let x_predict := gamma FM* x' FM+ u in
        let z_predict := H FM* x_predict in
        let p_predict :=  phi FM* P' FM* T(phi) FM+ gamma FM* w FM* T(w) FM* T(gamma) in
        let K := p_predict FM* T(H) FM* inv(H FM* p_predict FM* T(H) FM+ v FM* T(v)) in
        let x := x_predict FM+ K FM* (z FM- z_predict) in 
        let P := (FMIn FM- K FM* H) FM* p_predict in 
        (x,P)
end.
End KF_implement.



From Coq Require Extraction.
Extraction "KF.ml" KF_k.







(* 
Fixpoint KF_k (k:nat) (phi_l u_l gamma_l w_l H_l v_l: list R) (x0 P0: R):=
match k with
|O => (x0,P0)
|S n =>  let x' := fst (KF_k n phi_l u_l gamma_l w_l H_l v_l x0 P0) in
         let P' := snd (KF_k n phi_l u_l gamma_l w_l H_l v_l x0 P0) in
         let phi := nth n phi_l 0%R in 
         let u := nth n u_l 0%R in 
         let gamma := nth n gamma_l 0%R in
         let w := nth n w_l 0%R in
         let H := nth (S n) H_l 0%R in
         let v := nth (S n) v_l 0%R in
         let z := H * x' + v in
         let x_predict := gamma * x' + u in
         let z_predict := H * x_predict in
         let p_predict :=  phi * P' * phi + gamma * w * w * gamma in
         let K := p_predict * H / (H * p_predict * H + v * v) in
         let x := x_predict + K * (z - z_predict) in 
         let P := (1%R - K * H)* p_predict in 
         (x,P)
end.
Definition phi_l := [0;1;2;3].
Definition u_l := [0;1;2;3].
Definition gamma_l := [0;1;2;3].
Definition w_l := [0;1;2;3].
Definition v_l := [0;1;2;3].
Definition H_l := [0;1;2;3].

Compute KF_k 2 phi_l u_l gamma_l w_l H_l v_l 1 1.
 *)
