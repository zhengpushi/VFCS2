(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


   Ende 你好！
   我描述一下我的问题，放在 coq 脚本中可能容易一些。
   我在做控制系统中一些数学推导的形式验证，保证这些推导过程没有错误。
   以下是一个简单的示例
 *)

(** 主要使用 实数 *)
Require Import Reals.
Open Scope R.

(** 第一版实现，几乎纯依赖人力来检查 *)
Module Ver1.
  (** 假设将一些物理定律表达为函数 *)

  (** 力 Force (f), 质量 mass (m), 加速度 acc (a)。于是：f = m * a *)
  Definition Get_F_by_M_A (m a : R) : R := m * a.

  (** 然后，我定义了一些推导后的函数，如何证明这个推导是正确的？*)
  Definition Get_A_by_F_M (f m : R) : R := f / m.

  (** 使用一个手写的规范，来验证上述函数的推导正确 *)
  Lemma Get_A_by_F_M_ok : forall f m,
      m <> 0 ->
      (* 首先由 Get_A_by_F_M 算出一个 a *)
      let a := Get_A_by_F_M f m in
      (* 然后用 m 和算出的 a 代入第一个等式，证明结果相同 *)
      Get_F_by_M_A m a = f.
  Proof.
    intros. cbv in *. field. auto.
  Qed.

End Ver1.


(** 第2版实现，硬生生的加入了类型约束 *)
Module Ver2.

  (** 先把一些物理量声明为不同的类型，它们都携带一个 实数值 *)
  Inductive F := mk_F (val : R).
  Inductive M := mk_M (val : R).
  Inductive A := mk_A (val : R).

  (** 取出这些类型的项所携带的值，相当于是语义解释 *)
  Definition F2R (x:F) : R := let '(mk_F v) := x in v.
  Definition M2R (x:M) : R := let '(mk_M v) := x in v.
  Definition A2R (x:A) : R := let '(mk_A v) := x in v.
  
  (** 将 F,M,A 之间的联系用 归纳关系 来定义，称为规范 *)
  Inductive F_M_A_spec (f:F) (m:M) (a:A) : Prop :=
    F_M_A (_ : F2R f = (M2R m) * (A2R a)).

  (** 此时，可以定义更“安全”的函数 *)
  Definition get_F_by_M_A (m:M) (a:A) : F :=
    mk_F ((M2R m) * (A2R a)).

  (** 以下引理保证了 get_F_by_M_A 是满足规范的 *)
  Lemma get_F_by_M_A_spec : forall (m:M) (a:A),
      F_M_A_spec (get_F_by_M_A m a) m a.
  Proof.
    intros. constructor. cbv. auto.
  Qed.

End Ver2.

(** 我的问题是：
    1. 这种处理方式算是可靠吗？
    2. 实际问题中，有很多很多的变量 v1 v2 ... vn，
       假如有如下关系（或规范）：
         R1 v1 v2
         R2 v2 v3
       那么，我要给出一个 v1 和 v3 之间的关系式f(v1,v3)=0，此时，如何说明 f 的定义是可靠的？
       因为我并没有定义 v1 和 v3 之间的规范。
*)

(** 第3版实现，考虑多变量、传递性等 *)
Module Ver3.

  (** 物理量类别 (QuantityKind) *)
  Inductive QKind :=
  | Force
  | Mass
  | Acc
  | Velocity (* 速度 *)
  | Momentum (* 动量 *)
  .

  Scheme Equality for QKind.

  (** 数值型的物理量(NumberQuantity) *)
  Inductive NQ (k : QKind) :=
    mk_NQ (val : R -> R). (* 函数，表示随时间变化 *)

  (** 物理量的语义 *)
  Definition NQ2R {k : QKind} (q : NQ k) : R -> R :=
    let '(mk_NQ _ v) := q in v.

  (** 定义已知的关系，称为规范 *)
  Inductive Q_spec : Prop :=
    (* f = m * a *)
  | NewtonLaw2 (_ : forall (f : NQ Force) (m : NQ Mass) (a : NQ Acc) t,
          (NQ2R f t) = (NQ2R m t) * (NQ2R a t))
  (* p = m * v *)
  | MomentumLaw (_ : forall (p : NQ Momentum) (m : NQ Mass) (v : NQ Velocity) t,
          (NQ2R p t) = (NQ2R m t) * (NQ2R v t)).

  (** 此时，可以定义 F = m a, p = mv, 以及推导出
      m = F / a, v = p / m = (p*a)/F 等 *)

  (** F = m a *)
  Definition get_F_by_M_A (m:NQ Mass) (a:NQ Acc) : NQ Force :=
    mk_NQ _ (fun t => (NQ2R a t) * (NQ2R m t)).

  Lemma get_F_by_M_A_spec : Q_spec.
    (* 无法和 get_F_by_M_A 关联起来 *)
  Abort.

  (** 简单的方式，使用 Axiom *)

  (** 定义一组物理量之间的规范 *)
  Definition NewtonLaw2_spec (f : NQ Force) (m : NQ Mass) (a : NQ Acc) : Prop :=
    forall t, (NQ2R f t) = (NQ2R m t) * (NQ2R a t).

  (** 公理化的承认一些事实 *)
  Axiom NewtonLaw2_Rule : forall (f : NQ Force) (m : NQ Mass) (a : NQ Acc) t,
      (NQ2R f t) = (NQ2R m t) * (NQ2R a t).

  Lemma get_F_by_M_A_spec : forall (m:NQ Mass) (a:NQ Acc),
      NewtonLaw2_spec (get_F_by_M_A m a) m a.
  Proof.
    intros. unfold NewtonLaw2_spec. intros. rewrite (NewtonLaw2_Rule _ m a).
    auto.
  Qed.

  (** 另一个示例 *)

  (** 计算 acc *)
  Definition Get_A_by_F_M (f:NQ Force) (m:NQ Mass) : NQ Acc :=
    mk_NQ _ (fun t => (NQ2R f t) * (NQ2R m t)).

  Lemma Get_A_by_F_spec : forall (f:NQ Force) (m:NQ Mass),
      (forall t, NQ2R m t <> 0) ->
      NewtonLaw2_spec f m (Get_A_by_F_M f m).
  Proof.
    intros. unfold NewtonLaw2_spec. intros.
    eapply (NewtonLaw2_Rule f m _). (* 这一步肯定有问题，我特意把 Get_A_by_F_M 定义错误率。*)
    ?
  Qed.
