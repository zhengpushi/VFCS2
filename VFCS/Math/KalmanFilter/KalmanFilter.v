(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Kalman filter
  author    : Zhengpu Shi
  date      : 2023.03
  
  reference :
  1. ZhangZhen, https://gitee.com/nuaazz/kalman_filtering

 *)

Require Import MatrixRfun.

(*矩阵和向量维度*)
Variable n m: nat.

(* xk是k时刻的状态向量
xk1 是k-1时刻的状态向量 
uk1是k-1时刻的控制向量 
wk1是k-1时刻的系统噪声*)
(* Variable xk: @Mat (R->R) n 1. *)
Variable  xk1 uk1 wk1: mat n 1.

(*zk是k时刻的观测向量  
 vk是k时刻的观测噪声*)
Variables  vk : mat m 1.

(*phik1是k-1时刻到k时刻的系统转移矩阵 是不变的常数矩阵
gammak1是系统噪声矩阵 表征各噪声分别影响个状态的程度
Hk是k时刻的观测矩阵*)
Variable phik1 gammak1: mat n n. 
Variables Hk : mat m n.
(**连续时间线性系统**)
Section Chap8_2_3_Discrete_time_linear_system.
  


  (*离散时间线性系统模型 8.38*)
  (* xk = Φ *xk1 + uk1 + Γ*wk1 *)
  (* zk = H *xk + vk*)
  (* 
Axiom Discrete_time_linear_system_xk : xk == (phik1 * xk1) + uk1 + (gammak1 * wk1).
Axiom Discrete_time_linear_system_zk : zk == (Hk * xk) + vk. 
   *)
  (* xk是k时刻的状态向量 *)
  Definition xk := (phik1 * xk1) + uk1 + (gammak1 * wk1).
  Definition zk := (Hk * xk) + vk.
  
End Chap8_2_3_Discrete_time_linear_system.

Section Kalman_filtering.
  (* Exkk是k时刻状态的最小方差无偏估计  
     ESxkk1 是在上一时刻状态估计ESxk1k1 的基础上对当前时刻状态xk的一步预测 8.5.7*)
  (* Variable ESxkk : @Mat (R->R) n 1. *)
  (* Variable ESxkk1 : @Mat (R->R) n 1. *)
  Variable ESxk1k1 : mat n 1.

  (*----------------------------8.57-----------------------------*)
  (*  ESxkk1 = phi*ESxk1k1 + u                                   *)
  (*  ESzkk1 = H*ESxk1k1                                         *)
  (*  ESxkk1 是在上一时刻状态估计ESxk1k1 的基础上对当前时刻状态xk的一步预测*)
  (*  ESzkk1 是在ESxkk1的基础上对当前时刻zk的一步预测                  *)
  (*-------------------------------------------------------------*)
  Definition ESxkk1 := phik1 * ESxk1k1 + uk1.
  Definition ESzkk1 := Hk * ESxkk1.

  Variable Kk' Kk'': mat n n. 
  Variable Kk: mat n m.


  Definition In := @mat1 n .

  (*由于是线性估计器，估计EXxkk(estimate x_(k|k))可以表示未先验估计和观测值的线性组合形式  8.45
ESxkk = Kk' * Exk1k1 + Kkzk + Kk'' * uk1   *)
  Definition ESxkk := Kk' * ESxk1k1 + Kk * zk + Kk'' * uk1.

  (*------------------------*)
  (* 2 参数Kk' 和 Kk''的推导  *)
  (*------------------------*) 
  (**ERxkk为状态误差 8.47 **)
  (**ERxkk = xk - ESxkk **)
  (* Axiom ERxkk_847 :ERxkk ==  xk - ESxkk.
Axiom ERxk1k1_847 :ERxk1k1 ==  xk1 - ESxk1k1.
Axiom ERxkk1_847 :ERxkk1 ==  xk - ESxkk1. *)
  Definition ERxkk :=  xk - ESxkk.
  Definition ERxk1k1 :=  xk1 - ESxk1k1.
  Definition ERxkk1 :=  xk - ESxkk1.

  (*ESxkk 是xkk的无偏估计，则误差ERxkk=0 (Error x_(k|k))    8.46*)
  (*    8.46       *)
  Axiom ERxkk_eq0 : ERxkk == mat0.
  Axiom ERxk1k1_eq0 : ERxk1k1 == mat0. 

  Lemma error_x_kk_848 : ERxkk == xk - (Kk' * ESxk1k1 + Kk * zk + Kk'' * uk1).
  Proof.
    reflexivity.
  Qed.


  (*-----------3.1 8.49---------------*)
  Lemma error_xkk_3_1:
    ERxkk == 
      phik1 * xk1 + uk1 + gammak1 * wk1 - Kk' * ESxk1k1 - 
        Kk * (Hk * (phik1 * xk1 + uk1 + (gammak1 * wk1)) + vk) - Kk'' * uk1.
  Proof.
    unfold ERxkk.
    unfold ESxkk.
    unfold zk.
    unfold xk.
    rewrite !msub_assoc.
    (* reflexivity. *) (* it cannot be finished *)
    f_equiv. rewrite madd_assoc. easy.
  Qed.

  (** 交换半群上的自动证明方法探索，因 error_xkk_3_2 问题引起 *)
  Section develop_amonoid_auto_proof.
    Variable r c : nat.
    Variable m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 : mat r c.

    (** 消去头部(head)：解决 c + a2 = c + b2 *)
    Ltac elimh :=
      try rewrite !madd_assoc; (* maybe it is not a norm form *)
      match goal with
      | |- ?c + ?a2 == ?c + ?b2 => f_equiv
      end.
    (** 消去尾部(tail)：解决 a1 + c = b1 + c *)
    Ltac elimt :=
      try rewrite <- !madd_assoc;
      match goal with
      | |- ?a1 + ?c == ?a2 + ?c => f_equiv
      end;
      try rewrite !madd_assoc. (* restore the layout *)

    (** 颠倒顺序后消去：例如 a1 + (a2 + c) = (b1 + b2) + c，
        首先全部调整为左结合，然后消去尾巴 *)

    (** 注意：以下操作都是在右结合的规范化形式下而言，若不是则先自动使用结合律调整 *)
    
    (** 移至末尾：将任意单个元素移动到整个表达式的尾端
        转换 a1 + (... + (c + ...) ...)
        到   a1 + (... + (... + c) ...) *)
    Ltac move2t c :=
      rewrite ?madd_assoc;
      try rewrite (madd_comm c); rewrite ?madd_assoc.

    (** 移至头部：将任意单个元素移动到整个表达式的头部
        转换 a1 + (... + (... + c) ...)
        到   c + (a1 + (... + ...) ...) *)
    Ltac move2h c :=
      rewrite <- ?madd_assoc;
      try rewrite (madd_comm _ c); rewrite ?madd_assoc.      

    (** 这是 error_xkk_3_2 证明中抽取出的简化问题 *)

    Goal m0 + (m8 + (m1 + (m2 + (m3 + (m4 + (m5 + (m6 + m7)))))))
      == m0 + (m3 + (m2 + (m1 + (m5 + (m8 + (m4 + (m7 + m6))))))).
      (* 第1种策略，每次都消去头部 *)
      move2h m0; elimh.
      move2h m3; elimh.
      move2h m2; elimh.
      move2h m1; elimh.
      move2h m5; elimh.
      move2h m8; elimh.
      move2h m4; elimh.
      move2h m6; elimh.
      Restart.
      (* 第2种策略，每次都消去尾部 *)
      move2t m6; elimt.
      move2t m7; elimt.
      move2t m5; elimt.
      move2t m4; elimt.
      move2t m3; elimt.
      move2t m2; elimt.
      move2t m1; elimt.
      Restart.
      (* 第3种策略，自动每次都消去头部 *)
      rewrite ?madd_assoc;
      repeat match goal with
      | |- _ + _ == ?m + _ => move2h m; elimh
      end.
    Qed.

    (** 这里只考虑加法，减法、括号、乘法等在外面处理 *)
    Ltac solve_meq :=
      rewrite ?madd_assoc;
      repeat match goal with
        | |- _ + _ == ?m + _ => move2h m; elimh
        end.
      
    (** 更多测试 *)
    Goal m0 + (m1 + m2) + (m3 + m4) == m3 + (m1 + m4) + m0 + m2.
      solve_meq. Qed.
      
  End develop_amonoid_auto_proof.

  (** 一组用于解决矩阵等式的策略（不展开矩阵，只考虑符号上的处理）*)
  
  (** 移至头部：将任意单个元素移动到整个表达式的头部
        转换 a1 + (... + (... + c) ...)
        到   c + (a1 + (... + ...) ...) *)
  Ltac move2h c :=
    rewrite <- ?madd_assoc;
    try rewrite (madd_comm _ c); rewrite ?madd_assoc.      

  (** 消去头部(head)：解决 c + a2 = c + b2 *)
  Ltac elimh :=
    try rewrite !madd_assoc; (* maybe it is not a norm form *)
    match goal with
    | |- ?c + ?a2 == ?c + ?b2 => f_equiv
    end.

  (** 交换半群上的自动证明，仅是矩阵 *)
  Ltac amonoid_auto :=
    rewrite ?madd_assoc;
    repeat match goal with
      | |- _ + _ == ?m + _ => move2h m; elimh
      end.

  (** 将矩阵表达式的多项式转换到单项式：去掉减法，括号，
      注意，所有 (-a1)*a2 和 a1*(-a2) 都转化为 -(a1*a2) *)
  Ltac mat_poly2mono :=
    repeat rewrite
      ?msub_rw,              (* a - b = a + (-b) *)
      ?mmul_add_distr_l,     (* a * (b + c) = a * b + a * c *)
      ?mmul_add_distr_r,     (* (a + b) * c = a * c + b * c *)
      ?mopp_0,               (* - 0 = 0 *)
      ?mmul_1_r,             (* a * 1 = a *)
      ?mmul_1_l,             (* 1 * a = a *)
      ?mmul_0_r,             (* a * 0 = 0 *)
      ?madd_0_l,             (* 0 + a = a *)
      ?madd_0_r,             (* a + 0 = a *)
      ?mopp_add,             (* - (a + b) = -a + -b *)
      <- ?mopp_mul_l,        (* - (a * b) = a * (-b) *)
      <- ?mopp_mul_r,        (* - (a * b) = (-a) * b *)
      ?mopp_opp,             (* - - a = a *)
      ?mtrans_add,           (* (a + b)\T = a\T + b\T *)
      ?mtrans_opp,           (* (- a)\T = - (a\T) *)
      ?mtrans_mul,           (* (a * b)\T = b\T * a\T *)
      ?mtrans_0,             (* 0\T = 0 *)
      ?mtrans_1,             (* 1\T = 1 *)
      <- ?mmul_assoc.        (* (a * b) * c = a * (b * c) *)
  
  (** 非交换环上的证明，这里仅是矩阵的特例 *)
  (** 解决 meq：先展开减法、括号、乘法等，然后在纯 amonoid 上处理 *)
  Ltac solve_meq :=
    mat_poly2mono;
    amonoid_auto.

  (*----------------------------3.2  8.50---------------------------------*)
  (* ER = (phi-KHphi)xk1 - K'ES + (gamma-KHgamma)w + (I-KH-K'')u - Kv *)

  (* 最初始的证明方法，比较费力 *)
  Lemma error_xkk_3_2_first: ERxkk ==
                         (phik1 - Kk * Hk * phik1) * xk1 -
                           Kk' * ESxk1k1 +
                           (gammak1 - Kk * Hk * gammak1) * wk1 +
                           (In - Kk * Hk - Kk'' ) * uk1 - 
                           Kk * vk.
  Proof.
    rewrite error_xkk_3_1.
    rewrite ?mmul_sub_distr_r.
    rewrite ?mmul_add_distr_l.
    rewrite <- ?mmul_assoc.
    rewrite <- ?msub_assoc.
    rewrite <- ?msub_assoc1.
    rewrite mmul_1_l. rewrite ?msub_rw.
    rewrite ?madd_assoc. rewrite (madd_comm (-(Kk * vk))). rewrite <- ?madd_assoc.
    f_equiv. f_equiv.
    rewrite ?madd_assoc. f_equiv.
    rewrite (madd_comm (-(Kk * Hk * uk1))). rewrite <- ?madd_assoc. f_equiv.
    rewrite ?madd_assoc. rewrite madd_comm. rewrite <- ?madd_assoc. f_equiv. f_equiv.
    rewrite ?madd_assoc. rewrite madd_comm. rewrite <- ?madd_assoc. f_equiv.
    apply madd_comm.
  Qed.

  (* 改进的证明，使用了助记符，找到了一些规律 *)
  Lemma error_xkk_3_2_second: ERxkk ==
                         (phik1 - Kk * Hk * phik1) * xk1 -
                           Kk' * ESxk1k1 +
                           (gammak1 - Kk * Hk * gammak1) * wk1 +
                           (In - Kk * Hk - Kk'' ) * uk1 - 
                           Kk * vk.
  Proof.
    rewrite error_xkk_3_1.
    (* 先给出表达式的助记符，方便观看 *)
    remember phik1 as a.
    remember xk1 as b.
    remember uk1 as c.
    remember gammak1 as d.
    remember wk1 as e.
    remember Kk' as f.
    remember ESxk1k1 as g.
    remember Kk as h.
    remember Hk as i.
    remember Kk'' as j.
    remember vk as k.
    (* 去掉所有括号，减法等，变成单项式 *)
    rewrite ?msub_rw.
    rewrite ?mmul_add_distr_l.     (* a * (b + c) = a * b + a * c *)
    rewrite ?mmul_add_distr_r.     (* (a + b) * c = a * c + b * c *)
    rewrite ?mmul_1_l.             (* 1 * a = a *)
    rewrite ?mopp_add.             (* - (a + b) = -a + -b *)
    rewrite <- ?mopp_mul_l.        (* - (a * b) = a * (-b) *)
    rewrite <- ?mmul_assoc.        (* (a * b) * c = a * (b * c) *)
    (* 再给出一组助记符，表示每个单项式 *)
    remember (a * b).
    remember (d * e).
    remember (- (f * g)).
    remember (- (h * i * a * b)).
    remember (- (h * i * c)).
    remember (- (h * i * d * e)).
    remember (- (h * k)).
    remember (- (j * c)).
    remember c.
    (* 手动重写 *)
    rewrite ?madd_assoc; f_equiv.
    rewrite (madd_comm m6). rewrite <- ?madd_assoc. f_equiv. f_equiv.
    rewrite ?madd_assoc. rewrite (madd_comm m4). rewrite <- ?madd_assoc. f_equiv.
    rewrite (madd_comm _ m8). rewrite ?madd_assoc. f_equiv.
    rewrite <- ?madd_assoc. f_equiv.
    rewrite (madd_comm _ m3). rewrite ?madd_assoc. f_equiv.
    apply madd_comm.
  Qed.

  (* 几乎是自动化的证明，能够解决一类问题 *)
  Lemma error_xkk_3_2: ERxkk ==
                         (phik1 - Kk * Hk * phik1) * xk1 -
                           Kk' * ESxk1k1 +
                           (gammak1 - Kk * Hk * gammak1) * wk1 +
                           (In - Kk * Hk - Kk'' ) * uk1 - 
                           Kk * vk.
  Proof.
    rewrite error_xkk_3_1.
    solve_meq.
  Qed.

  (*------------------------4.22----8.51-------------------------------------------*)
  (* ER = (phi-KHphi-K')xk1 + K'(xk1-ES) + (gamma-KHgamma)w + (I-KH-K'')u - Kv *)
  Lemma error_xkk_4_22_first: ERxkk ==
                          (phik1 - Kk * Hk * phik1 - Kk') * xk1 +
                            Kk' * (xk1 - ESxk1k1) +
                            (gammak1 - Kk * Hk * gammak1) * wk1 +
                            (In - Kk * Hk - Kk'' ) * uk1 - 
                            Kk * vk.
  Proof.
    rewrite error_xkk_3_2.
    solve_meq.
    (* 又发现了一些问题 *)
    rewrite <- ?madd_assoc. rewrite madd_opp_l. rewrite madd_0_l.
    solve_meq.
  Qed.

  (** 矩阵零元和逆元的化简 *)
  (* Ltac solve_mat_0_1 := *)
  (*   (rewrite ?madd_assoc, ?madd_opp_l, ?madd_0_l, ?mmul_0_l); *)
  (*   (rewrite <- ?madd_assoc, ?madd_opp_r, ?madd_0_r, ?mmul_0_r). *)

  Ltac solve_mat_0_1 :=
    (rewrite ?madd_assoc,
      ?madd_opp_l, ?madd_0_l, ?mmul_0_l, ?madd_opp_r, ?madd_0_r, ?mmul_0_r);
    (rewrite <- ?madd_assoc,
      ?madd_opp_l, ?madd_0_l, ?mmul_0_l, ?madd_opp_r, ?madd_0_r, ?mmul_0_r).

  (** 更新的 meq 求解 *)
  Ltac solve_meq' :=
    mat_poly2mono;
    repeat (solve_mat_0_1; amonoid_auto); try easy.

  (* 再次证明 *)
  Lemma error_xkk_4_22: ERxkk ==
                                (phik1 - Kk * Hk * phik1 - Kk') * xk1 +
                                  Kk' * (xk1 - ESxk1k1) +
                                  (gammak1 - Kk * Hk * gammak1) * wk1 +
                                  (In - Kk * Hk - Kk'' ) * uk1 - 
                                  Kk * vk.
  Proof.
    rewrite error_xkk_3_2.
    solve_meq'.
  Qed.

  Lemma error_x_kk_852: ERxkk ==
                          (phik1 - Kk * Hk * phik1 - Kk') * xk1 +
                            (In - Kk * Hk - Kk'' ) * uk1 +
                            Kk' * (xk1 - ESxk1k1) +
                            (gammak1 - Kk * Hk * gammak1) * wk1  - 
                            Kk * vk.
  Proof.
    rewrite error_xkk_4_22.
    solve_meq.
  Qed.

  (*卡尔曼滤波器要求wk和vk是互不相关的零均值高斯白噪声序列，即 vk=0 wk=0 8.39*)
  Axiom v_eq0:  vk == mat0.
  Axiom w_eq0: wk1 == mat0.

  (*-----------------------4.23-----8.53---------------------------------------*)
  (*  (phi-KHphi-K')xk1 + (I-KH-K'')u=0                                        *)
  (*---------------------------------------------------------------------------*)
  Lemma eq0_423: (phik1 - Kk * Hk * phik1 - Kk') * xk1 + (In - Kk * Hk - Kk'' ) * uk1 == mat0.
  Proof.
    rewrite <- ERxkk_eq0.
    rewrite error_x_kk_852.
    assert(ERxk1k1 == xk1 - ESxk1k1). {reflexivity. }
    rewrite <- H.
    rewrite v_eq0,w_eq0,ERxk1k1_eq0.
    solve_meq'.
  Qed.


  (*xk1 和 uk1 分别为系统的状态向量和控制向量，不能时刻为0 *)
  Axiom noteq0_xk1 : not(xk1 == mat0).
  Axiom noteq0_uk1 : not(uk1 == mat0).

  (*  A*B + C*D = 0 .B D不等于0 ->  A C 等于0*)
  Axiom eq0:forall {n m p:nat} (A C:@mat m n) (B D:@mat n p),
      A * B + C * D == mat0 ->
      not(B == mat0) -> not(D == mat0) -> A == mat0 /\ C == mat0.

  (*----------------------------8.54-------------------*)
  (*  (phi-KHphi-K')xk1 =0                             *)
  (*  (I-KH-K'')u=0                                    *)
  (*---------------------------------------------------*)

  Lemma eq0_854_1:  phik1 - Kk * Hk * phik1 - Kk' == mat0.
  Proof.
    apply (eq0  (phik1 - Kk * Hk * phik1 - Kk')  (In - Kk * Hk - Kk'') xk1 uk1).
    apply eq0_423. apply noteq0_xk1. apply noteq0_uk1.
  Qed.

  Lemma eq0_854_2: In - Kk * Hk - Kk'' == mat0.
    apply (eq0  (phik1 - Kk * Hk * phik1 - Kk')  (In - Kk * Hk - Kk'') xk1 uk1).
    apply eq0_423. apply noteq0_xk1. apply noteq0_uk1.
  Qed.


  (*----------------------------8.55-------------------*)
  (*  K'=phi-KHphi                                     *)
  (*  K''=I-KH                                         *)
  (*---------------------------------------------------*)
  Lemma Kk'_4_5: Kk' == phik1 - Kk * Hk * phik1.
  Proof.
    assert(phik1 - Kk * Hk * phik1 - Kk' + Kk' == mat0 + Kk').
    { f_equiv.
      apply eq0_854_1.
    }
    rewrite madd_0_l in H. rewrite <- H. solve_meq'.
  Qed.
  
  Lemma Kk''_4_5:  Kk'' == In - Kk * Hk.
  Proof.
    assert(In - Kk * Hk - Kk''  + Kk''  == mat0 + Kk'').
    {
      f_equiv. apply eq0_854_2.
    }
    rewrite madd_0_l in H. rewrite <- H. solve_meq'.
  Qed.

  (*-----------------4.26-------8.56-------------------*)
  (* ESxkk = ESxkk1 + K(z - ESzkk1)                    *)
  (*---------------------------------------------------*)

  Lemma estimate_xkk_4_26: ESxkk == ESxkk1 + Kk *(zk - ESzkk1).
  Proof.
    unfold ESxkk.
    rewrite Kk'_4_5,Kk''_4_5.
    unfold ESxkk1,ESzkk1,ESxkk1. solve_meq'.
  Qed.

  (*-------------------*)
  (* 3 参数Kk的推导      *)
  (*-------------------*) 

  Definition Pkk := ERxkk * ERxkk\T.
  Definition Pkk1 := ERxkk1 * ERxkk1\T.
  Definition Rk := vk * vk\T.

  (*----------------4.31--------8.59-------------------*)
  (* ERxkk = (I-KH)ERxkk1 - Kv                         *)
  (*---------------------------------------------------*)

  Lemma error_xkk_4_31: ERxkk == (In - Kk * Hk) * ERxkk1 - Kk * vk.
  Proof.
    unfold ERxkk.
    rewrite estimate_xkk_4_26.
    unfold ESzkk1.
    unfold zk. unfold ERxkk1. solve_meq'.
  Qed.

  (*----------------------------8.60------------------------*)
  (* ERxkk * T_ERxkk = (I-KH) * ERxkk1 * T_ERxkk * T_(I-KH) *)         
  (*                 - (I-KH)ERxkk1 * T_v * T_K             *)
  (*                 - K * v * T_ERxkk*T_(I-KH)             *)
  (*                 + K * v * T_v * T_K                    *)
  (*--------------------------------------------------------*)
  Lemma ERxkk_mul_T_ERxkk_860:
    ERxkk * ERxkk\T == 
      (In - Kk * Hk) * ERxkk1 * ERxkk1\T * (In - Kk * Hk)\T 
      - (In - Kk * Hk) * ERxkk1 * vk\T * Kk\T 
      - Kk * vk * ERxkk1\T * (In - Kk * Hk)\T 
      + Kk * vk * vk\T * Kk\T.
  Proof.
    assert(ERxkk\T == ERxkk1\T * (In - Kk * Hk)\T - vk\T * Kk\T).
    {
      rewrite error_xkk_4_31. solve_meq'.
    }
    rewrite H.
    rewrite error_xkk_4_31.
    solve_meq'.
  Qed.
  
  (*----------------------------8.61------------------*)
  (* ERxkk 与噪声vk 无关                                *)
  (* ERxkk * T_v = 0                                   *)
  (* v * T_ERxkk =0                                    *)
  (*---------------------------------------------------*)

  Axiom ERxkk1_Tv_eq0:ERxkk1 * vk\T == mat0.
  Axiom v_TERxkk1_eq0:vk * ERxkk1\T == mat0.

  (*----------------4.33--------8.62------------------------*)
  (* Pkk = (I-KH) * Pkk1 * T_(I-KH)                         *)         
  (*                 + K * R * T_K                          *)
  (*--------------------------------------------------------*)
  Lemma Pkk_4_33: Pkk == (In - Kk * Hk) * Pkk1 * (In - Kk * Hk)\T  + Kk * Rk * Kk\T.
  Proof.
    unfold Pkk,Pkk1,Rk.
    rewrite ERxkk_mul_T_ERxkk_860.
    rewrite (mmul_assoc _ ERxkk1 (vk\T)).
    rewrite (mmul_assoc _ vk (ERxkk1\T)).
    rewrite ERxkk1_Tv_eq0,v_TERxkk1_eq0.
    solve_meq'. solve_meq'.
  Qed.

  Definition Pk1k1 := ERxk1k1 * (ERxk1k1)\T.
  Definition Qk1 := wk1 * (wk1)\T.


  (*----------------------------8.67------------------------------------------------------*)
  (*Pkk = Pkk1 - Pkk1 * T(H) * T(K) - K * H * Pkk1 + K *(H * Pkk1 * T(H) + R) * T(K)      *)
  (*--------------------------------------------------------------------------------------*)
  Lemma Pkk_867: Pkk == Pkk1 - 
                           Pkk1 * (Hk)\T * (Kk)\T - 
                           Kk * Hk * Pkk1 + 
                           Kk * ( Hk * Pkk1 * (Hk)\T + Rk) * (Kk)\T.
  Proof.
    rewrite Pkk_4_33.
    assert((In - Kk * Hk)\T == In - (Hk)\T * (Kk)\T).
    { solve_meq'. }
    rewrite H. solve_meq'.
  Qed.


  (*tr(Pkk) = tr(Pkk1) - tr(P*T_H*T_K) - tr(KHP) + tr(K(HPT_H)T_K) *)
  Lemma tr_Pkk_867:
    tr(Pkk)  =
      (tr(Pkk1) - tr(Pkk1 * Hk\T * Kk\T)%M  - tr(Kk * Hk * Pkk1)%M  +
        tr(Kk * ( Hk * Pkk1 * Hk\T + Rk) * Kk\T)%M)%F.
  Proof.
    assert(tr(Pkk) = tr(Pkk1 - Pkk1 * (Hk)\T * (Kk)\T - 
                          Kk * Hk * Pkk1 + 
                          Kk * ( Hk * Pkk1 * (Hk)\T + Rk) * (Kk)\T)).
    { f_equiv. apply Pkk_867. }
    rewrite H. rewrite mtrace_add. rewrite ?mtrace_sub. solve_meq'.
  Qed.

  (* tr P*T_H*T_K = tr KHP*)
  Lemma tr_KHP_eq: tr(Pkk1 * (Hk)\T * (Kk)\T) = tr(Kk * Hk * Pkk1) .
  Proof.
    assert(Pkk1 * ( Hk)\T * ( Kk)\T == (Kk * Hk * Pkk1)\T).
    { rewrite mtrans_mul.
      unfold Pkk1.
      rewrite mtrans_mul. rewrite mtrans_trans. solve_meq'. }
    rewrite H. rewrite mtrace_trans. auto.
  Qed.

  (*tr(Pkk) = tr(Pkk1) -2* tr(KHP) + tr(K(HPT_H)T_K) *)
  Lemma tr_Pkk_867_1 :
    tr(Pkk)  =
      (tr(Pkk1) - 
        2 n* (tr(Kk * Hk * Pkk1)%M) +
        tr(Kk * ( Hk * Pkk1 * (Hk)\T + Rk) * (Kk)\T)%M)%F.
  Proof.
    rewrite tr_Pkk_867.
    rewrite tr_KHP_eq. simpl.
    unfold fsub. ring.
  Qed.

  (* (*Deri(tr(Pkk))/Deri Kk = 2K(HPT(H)+R) -2*T(P)T(H)  *) *)
  (* Lemma Deri_Pkk_867: Deri ( tr(Pkk) ) Kk ==  *)
  (*                       FMtwoMat (Kk * ( Hk * Pkk1 * T(Hk) + Rk)) -  *)
  (*                         FMtwoMat (T(Pkk1) * T(Hk)). *)
  (* Proof. *)
  (*   rewrite FMat_Deri_compat with (mx':= (Pkk1 - Pkk1 * T(Hk) * T(Kk) -  *)
  (*                                           Kk * Hk * Pkk1 + Kk * ( Hk * Pkk1 * T(Hk) + Rk) * T(Kk))). *)
  (*   2:{ apply Pkk_867. } *)
  (*   rewrite ?FMat_Deri_add. *)
  (*   rewrite ?FMat_Deri_sub. *)
  (*   rewrite FMat_Deri_not_correlation. *)
  (*   rewrite FMat_Deri_compat' with (x':=tr(Kk * Hk * Pkk1)).  *)
  (*   2:{ apply tr_KHP_eq. } *)
  (*   rewrite FMat_Deri_compat with (mx':= Kk * (Hk * Pkk1)). *)
  (*   rewrite FMat_Deri_mul. *)
  (*   2:{ apply FMmul_assoc. } *)
  (*   rewrite FMat_Deri_trans_eq. *)
  (*   2:{  *)
  (*     unfold Rk. *)
  (*     unfold Pkk1. *)
  (*     rewrite FMteq_add. *)
  (*     rewrite ?FMteq_mul. *)
  (*     rewrite ?FMtteq. *)
  (*     rewrite <-FMmul_assoc. *)
  (*     reflexivity. *)
  (*   } *)
  (*   rewrite FMat_Deri_compat with (mx':= Kk * (Hk * Pkk1)). *)
  (*   2:{ apply FMmul_assoc. } *)
  (*   rewrite FMat_Deri_mul. *)
  (*   rewrite ?FMteq_mul. *)
  (*   rewrite FMadd_comm. *)
  (*   rewrite <- ?FMadd_assoc1. *)
  (*   rewrite FMadd_zero_r. *)
  (*   unfold FMtwoMat. *)
  (*   unfold FMatrix.twoMat. *)
  (*   unfold twoMat. *)
  (*   rewrite <- FMsub_assoc. *)
  (*   reflexivity. *)
  (* Qed. *)




End Kalman_filtering.

(* Require Import Matrix.inv. *)



(** 学习一下这个函数的结构 *)
Parameter inv : forall {n m :nat}, mat n m -> mat m n.

(* 原始版本 *)
Section KF_implement_v1.
  Fixpoint KF_k_v1 (k:nat)
    (u_l w_l: list (mat n 1))
    (v_l z_l: list (mat m 1))
    (phi_l gamma_l: list (mat n n))
    (H_l: list (mat m n))
    (x0: mat n 1) (P0: mat n n)
    : mat n 1 * mat n n := 
    match k with
    | O => (x0,P0)
    | S k' =>
        let x' := fst (KF_k_v1 k' u_l w_l v_l z_l phi_l gamma_l H_l x0 P0) in
        let P' := snd (KF_k_v1 k' u_l w_l v_l z_l phi_l gamma_l H_l x0 P0) in
        let phi := nth k' phi_l (@mat0 n n) in 
        let u := nth k' u_l (@mat0 n 1) in 
        let gamma := nth k' gamma_l (@mat0 n n)  in
        let w := nth k' w_l (@mat0 n 1) in
        let H := nth k H_l (@mat0 m n) in
        let v := nth k v_l (@mat0 m 1) in
        let z := nth k z_l (@mat0 m 1) in
        let x_predict := gamma * x' + u in
        let z_predict := H * x_predict in
        let p_predict :=  phi * P' * phi\T + gamma * w * w\T * gamma\T in
        let K := p_predict * H\T * inv(H * p_predict * H\T + v * v\T) in
        let x := x_predict + K * (z - z_predict) in 
        let P := ((@mat1 n) - K * H) * p_predict in 
        (x,P)
    end.
End KF_implement_v1.

(* 使用局部变量的版本 *)
Section KF_implement_v2.
  (* 离散时间线性系统模型 :
     xk = Φk' * xk' + uk' + Γk' * wk'
     zk = Hk * xk + vk
     其中，xk∈ ℝ a__b

   *)

  Variable u_l: list (mat n 1). (* 控制向量 *)
  Variable w_l: list (mat n 1). (* 系统噪声 *)
  Variable H_l: list (mat m n). (* 观测矩阵 *)
  Variable z_l: list (mat m 1). (* 观测向量 *)
  Variable v_l: list (mat m 1). (* 观测噪声 *)
  Variable phi_l: list (mat n n). (* 不变的常数矩阵 *)
  Variable gamma_l: list (mat n n). (* 系统噪声矩阵，各噪声分别影响各状态的程度 *)
  Variable x0: mat n 1.
  Variable P0: mat n n.
  
  Fixpoint KF_k_v2 (k:nat) : mat n 1 * mat n n := 
    match k with
    | O => (x0,P0)
    | S k' =>
        (* 递归计算 *)
        let x' := fst (KF_k_v2 k') in (* 系统的上一个状态 *)
        let P' := snd (KF_k_v2 k') in
        let u := nth k' u_l (@mat0 n 1) in (* 系统的控制输入 *)
        let v := nth k v_l (@mat0 m 1) in
        let phi := nth k' phi_l (@mat0 n n) in 
        let gamma := nth k' gamma_l (@mat0 n n)  in
        let H := nth k H_l (@mat0 m n) in
        let w := nth k' w_l (@mat0 n 1) in
        let z := nth k z_l (@mat0 m 1) in (* k时刻的观测值 *)
        (* 计算 *)
        let x_predict := (* 状态估计预测 *)
          gamma * x' + u in
        let z_predict := H * x_predict in  (* ? *)
        let p_predict :=  (* 误差协方差预测 *)
          phi * P' * phi\T + gamma * w * w\T * gamma\T in
        let K := (* 卡尔曼增益矩阵 *)
          p_predict * H\T * inv(H * p_predict * H\T + v * v\T) in
        let x := (* 系统的状态 *)
          x_predict + K * (z - z_predict) in 
        let P := (* 协方差阵 *)
          ((@mat1 n) - K * H) * p_predict in 
        (x,P)
    end.
  
End KF_implement_v2.


From Coq Require Extraction.
(* Recursive Extraction KF_k_v2. *)
Extraction "KF.ml" KF_k_v2.







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
