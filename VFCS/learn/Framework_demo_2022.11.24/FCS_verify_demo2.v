(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


FCS验证模型思路

    要解决的问题模型：
    假定一个大型系统，内部状态可以用一组实数变量值来表示，比如{v0,v1,...,vn}
    任意时刻，{v0,v1,...,vn} 都是确定的。
    其中，有些是已知值，比如飞行器质量，电机KV值等，
    大多数是随时变化的。
    但是，能够确定的是一组组等式或不等式，比如 {
    E1:f(v0,v1,..,vk) = 0
    ...
    Em: ...
    I1:f(vi,vk..) <= g(vm,..,vo)
    现在，需要根据这些已知条件来给出一组函数，能够给出新的求解方法。

    比如，定义了 get_A_by_B B = 2 * (B + 3) 这样的函数，其中，B和返回值都是R类型。
    实际调用时，如何确保输入的B就是我们需要的B的语义呢？

    这里，探索能否依靠类型系统来做这样的约束。
    方法1：为每个变量用Inductive定义一个类型。
    方法2：使用依赖类型来统一的定义。
。*)

Require Import Psatz.
Require Import Reals.
Open Scope R.


(** 用 typeclasses 定义一个类，表示可以转换为 R *)
Section RConvertable.
  
  Class RConvertable (A:Type) := {
      toR : A -> R
    }.
  
  Inductive Color := Red | Green | Blue.

  Instance Color_RConvertable : RConvertable Color := {
      toR := fun c => match c with
                    | Red => 1.0
                    | Green => 2.0
                    | Blue => 3.0
                    end
    }.

  Let color1 := Red.
  Let color2 := Green.

  Goal (toR color1) + (toR color2) = 3.0.
  Proof. cbv. ring. Qed.

End RConvertable.


(** 推进子系统：一个不考虑时间的简单系统，只考虑变量之间的代数关系推导 *)
Module PropulsionSystem.

  (** 常量 *)
  Parameter Pa0 : R.    (* 标准大气强，=101325 Pa *)
  Parameter rho0 : R.   (* 标准大气密度，=1.293kg/m^3 *)
  Parameter n_r : R.    (* 旋翼数目 *)
  Parameter T0 : R.    (* 温度常数，= 273 K *)

  (** 合理的假设 *)
  Hypotheses Pa0_gt0 : 0 < Pa0.

  (** 利用 Module 来防止命名空间污染，同时也作为软件构造的架构 *)
  
  (** 【环境】*)
  Module Env.

    (** 大气密度 *)
    Inductive Rho := mkRho (v : R).

    (** 这里手写 Rho -> R 的转换。在后面会有 RConvertable 的做法。
        使用 Coercion 的优点是自动类型转换，调用处的代码比较简洁 *)
    Definition Rho2R (x : Rho) : R := let '(mkRho v) := x in v.
    Coercion Rho2R : Rho >-> R.


    (** 温度 *)
    Inductive Temp := mkTemp (v : R).

    (** 这里采用 RConvertable 的做法，好处是代码比较规范，
        缺点是需要手动调用 toR 函数。 *)
    Global Instance Temp_Rconvertable : RConvertable Temp := {
        toR := fun x => let '(mkTemp v) := x in v
      }.
    (** 当然，也可以结合 Coercion 优点，将 toR 声明为 Coercion。
        但是失败了 *)
    Fail Coercion toR : Temp >-> R.

    (** 还是使用手写 Coercion 的方式吧 *)
    Definition Temp2R (x : Temp) : R := let '(mkTemp v) := x in v.
    Coercion Temp2R : Temp >-> R.

    
    (** 大气压强 *)
    Inductive Pa := mkPa (v : R).
    Definition Pa2R (x : Pa) : R := let '(mkPa v) := x in v.
    Coercion Pa2R : Pa >-> R.
    

    (** 飞行器高度（暂不区分各种类型的高度：绝对、相对、海拔等） *)
    Inductive Height := mkHeight (v : R).
    Definition Height2R (x : Height) : R := let '(mkHeight v) := x in v.
    Coercion Height2R : Height >-> R.

    
    (** 定义规范。这些需要人为检查 *)

    (** 定义了 Pa, Temp, Height 三者之间的关系 *)
    Inductive Pa_Temp_Height_spec (P_a:Pa) (T_t:Temp) (h:Height) : Prop :=
    | Pa_Temp_Height
        (H: T0 + T_t <> 0 ->
            (P_a:R) = Pa0 * (Rpower (1 - 0.0065 * (h / (T0 + T_t))) 5.2561)).
    
    (** 上面通过简单的类型系统来区分了变量类别，下面举例说明这种效果 *)

    (** 根据 Temp 和 Height 来计算 Pa *)
    Definition get_Pa_by_Temp_Height (t:Temp) (h:Height) : Pa :=
      (* 注意，我这里改了变量名，还有原本的 T0 + t 改成了 t + T0，
         以便说明我们是可以根据理论来定义需要的函数的 *)
      mkPa (Pa0 * (Rpower (1 - 0.0065 * (h / (t + T0))) 5.2561)).
    
    (** 证明这个定义正确 *)
    Lemma get_Pa_by_Temp_Height_ok : forall (T_t:Temp) (h:Height),
        Pa_Temp_Height_spec (get_Pa_by_Temp_Height T_t h) T_t h.
    Proof.
      constructor. cbn. intros. f_equal. f_equal. field. auto.
    Qed.

    (** 根据 Pa 和 Temp 来计算 Height *)
    Definition get_Height_by_Pa_Temp (pa:Pa) (t:Temp) : Height :=
      mkHeight ((t + T0) * (1 - Rpower (pa/Pa0) (1/5.2561)) / 0.0065).

    (** 注意，这里 0 < pa 的条件，是在证明中发现的。
        在实际编程中，如何利用这个前提来防止错误？暂时没有思路。
        另外，从OCaml的测试结果来看，0 < pa 好像没有必要，pa = 0 也不会有错，
        从数学公式也可以分析得到。
     *)
    Lemma get_Height_by_Pa_Temp_ok : forall (pa:Pa) (t:Temp),
        0 < pa -> Pa_Temp_Height_spec pa t (get_Height_by_Pa_Temp pa t).
    Proof.
      constructor. intros. cbn.
      replace (t + T0) with (T0 + t); try ring.
      remember (T0 + t) as t'.
      replace (0.0065 * (t' * (1 - Rpower (pa/Pa0) (1 / 5.2561)) / 0.0065 / t'))
        with (1 - Rpower (pa/Pa0) (1 / 5.2561)); try field; [|split; lra].
      replace (1 - (1 - Rpower (pa/Pa0) (1 / 5.2561)))
        with (Rpower (pa/Pa0) (1 / 5.2561)); try field.
      rewrite Rpower_mult.
      replace (1 / 5.2561 * 5.2561) with 1; [|field; lra].
      rewrite Rpower_1; try field.
      - pose (Pa0_gt0). lra.
      - pose (Pa0_gt0).
        apply Rdiv_lt_0_compat.
        auto. (* 这一步发现需要 0 < pa 的假设 *)
        auto.
    Qed.

  End Env.


End PropulsionSystem.


(** 来做一些例子 *)

(** ** Ex1: 已知 Pa、Temp，计算 Height *)
Section Ex1.
  Definition pa :=  PropulsionSystem.Env.mkPa 0.
  Definition temp := PropulsionSystem.Env.mkTemp 1.

  Definition height := PropulsionSystem.Env.get_Height_by_Pa_Temp pa temp.

End Ex1.

(** ** Ex2 代码抽取 *)
Require Import Extraction.

(* constant - Real number and operations *)
Extract Constant R => float.

(* (* patch for coq 8.11 and newer *) *)
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
Extract Constant pow => 
  "fun r0 n -> if n=0 then 1.0 else (r0 *. (pow r0 (n-1)))".

(* Extraction Inline  *)
(*   C_d C_fd  H_p D_p K0 e A epsilon alpha0. *)

(* Extract Constant P_a0 => "val_P_a0". *)
(* Extract Constant T0 => "val_T0". *)
(* Extract Constant e => "val_e". *)
(* Extract Constant rho0 => "val_rho0". *)
(* Extract Constant h => "val_h". *)
(* Extract Constant T_t => "val_T_t". *)
(* Extract Constant n_r => "val_n_r". *)

Extract Constant PropulsionSystem.Pa0 => "101325.0".
Extract Constant PropulsionSystem.T0 => "273.15".
Extract Constant PropulsionSystem.rho0 => "1.293".
Extract Constant PropulsionSystem.n_r => "4.0".

Extract Constant total_order_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)".

Extraction "FCS_verify_demo2.ml"  PropulsionSystem height.
