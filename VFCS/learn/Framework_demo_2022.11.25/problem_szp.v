(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


   Ende ��ã�
   ������һ���ҵ����⣬���� coq �ű��п�������һЩ��
   ����������ϵͳ��һЩ��ѧ�Ƶ�����ʽ��֤����֤��Щ�Ƶ�����û�д���
   ������һ���򵥵�ʾ��
 *)

(** ��Ҫʹ�� ʵ�� *)
Require Import Reals.
Open Scope R.

(** ��һ��ʵ�֣�������������������� *)
Module Ver1.
  (** ���轫һЩ�����ɱ��Ϊ���� *)

  (** �� Force (f), ���� mass (m), ���ٶ� acc (a)�����ǣ�f = m * a *)
  Definition Get_F_by_M_A (m a : R) : R := m * a.

  (** Ȼ���Ҷ�����һЩ�Ƶ���ĺ��������֤������Ƶ�����ȷ�ģ�*)
  Definition Get_A_by_F_M (f m : R) : R := f / m.

  (** ʹ��һ����д�Ĺ淶������֤�����������Ƶ���ȷ *)
  Lemma Get_A_by_F_M_ok : forall f m,
      m <> 0 ->
      (* ������ Get_A_by_F_M ���һ�� a *)
      let a := Get_A_by_F_M f m in
      (* Ȼ���� m ������� a �����һ����ʽ��֤�������ͬ *)
      Get_F_by_M_A m a = f.
  Proof.
    intros. cbv in *. field. auto.
  Qed.

End Ver1.


(** ��2��ʵ�֣�Ӳ�����ļ���������Լ�� *)
Module Ver2.

  (** �Ȱ�һЩ����������Ϊ��ͬ�����ͣ����Ƕ�Я��һ�� ʵ��ֵ *)
  Inductive F := mk_F (val : R).
  Inductive M := mk_M (val : R).
  Inductive A := mk_A (val : R).

  (** ȡ����Щ���͵�����Я����ֵ���൱����������� *)
  Definition F2R (x:F) : R := let '(mk_F v) := x in v.
  Definition M2R (x:M) : R := let '(mk_M v) := x in v.
  Definition A2R (x:A) : R := let '(mk_A v) := x in v.
  
  (** �� F,M,A ֮�����ϵ�� ���ɹ�ϵ �����壬��Ϊ�淶 *)
  Inductive F_M_A_spec (f:F) (m:M) (a:A) : Prop :=
    F_M_A (_ : F2R f = (M2R m) * (A2R a)).

  (** ��ʱ�����Զ��������ȫ���ĺ��� *)
  Definition get_F_by_M_A (m:M) (a:A) : F :=
    mk_F ((M2R m) * (A2R a)).

  (** ��������֤�� get_F_by_M_A ������淶�� *)
  Lemma get_F_by_M_A_spec : forall (m:M) (a:A),
      F_M_A_spec (get_F_by_M_A m a) m a.
  Proof.
    intros. constructor. cbv. auto.
  Qed.

End Ver2.

(** �ҵ������ǣ�
    1. ���ִ���ʽ���ǿɿ���
    2. ʵ�������У��кܶ�ܶ�ı��� v1 v2 ... vn��
       ���������¹�ϵ����淶����
         R1 v1 v2
         R2 v2 v3
       ��ô����Ҫ����һ�� v1 �� v3 ֮��Ĺ�ϵʽf(v1,v3)=0����ʱ�����˵�� f �Ķ����ǿɿ��ģ�
       ��Ϊ�Ҳ�û�ж��� v1 �� v3 ֮��Ĺ淶��
*)

(** ��3��ʵ�֣����Ƕ�����������Ե� *)
Module Ver3.

  (** ��������� (QuantityKind) *)
  Inductive QKind :=
  | Force
  | Mass
  | Acc
  | Velocity (* �ٶ� *)
  | Momentum (* ���� *)
  .

  Scheme Equality for QKind.

  (** ��ֵ�͵�������(NumberQuantity) *)
  Inductive NQ (k : QKind) :=
    mk_NQ (val : R -> R). (* ��������ʾ��ʱ��仯 *)

  (** ������������ *)
  Definition NQ2R {k : QKind} (q : NQ k) : R -> R :=
    let '(mk_NQ _ v) := q in v.

  (** ������֪�Ĺ�ϵ����Ϊ�淶 *)
  Inductive Q_spec : Prop :=
    (* f = m * a *)
  | NewtonLaw2 (_ : forall (f : NQ Force) (m : NQ Mass) (a : NQ Acc) t,
          (NQ2R f t) = (NQ2R m t) * (NQ2R a t))
  (* p = m * v *)
  | MomentumLaw (_ : forall (p : NQ Momentum) (m : NQ Mass) (v : NQ Velocity) t,
          (NQ2R p t) = (NQ2R m t) * (NQ2R v t)).

  (** ��ʱ�����Զ��� F = m a, p = mv, �Լ��Ƶ���
      m = F / a, v = p / m = (p*a)/F �� *)

  (** F = m a *)
  Definition get_F_by_M_A (m:NQ Mass) (a:NQ Acc) : NQ Force :=
    mk_NQ _ (fun t => (NQ2R a t) * (NQ2R m t)).

  Lemma get_F_by_M_A_spec : Q_spec.
    (* �޷��� get_F_by_M_A �������� *)
  Abort.

  (** �򵥵ķ�ʽ��ʹ�� Axiom *)

  (** ����һ��������֮��Ĺ淶 *)
  Definition NewtonLaw2_spec (f : NQ Force) (m : NQ Mass) (a : NQ Acc) : Prop :=
    forall t, (NQ2R f t) = (NQ2R m t) * (NQ2R a t).

  (** �����ĳ���һЩ��ʵ *)
  Axiom NewtonLaw2_Rule : forall (f : NQ Force) (m : NQ Mass) (a : NQ Acc) t,
      (NQ2R f t) = (NQ2R m t) * (NQ2R a t).

  Lemma get_F_by_M_A_spec : forall (m:NQ Mass) (a:NQ Acc),
      NewtonLaw2_spec (get_F_by_M_A m a) m a.
  Proof.
    intros. unfold NewtonLaw2_spec. intros. rewrite (NewtonLaw2_Rule _ m a).
    auto.
  Qed.

  (** ��һ��ʾ�� *)

  (** ���� acc *)
  Definition Get_A_by_F_M (f:NQ Force) (m:NQ Mass) : NQ Acc :=
    mk_NQ _ (fun t => (NQ2R f t) * (NQ2R m t)).

  Lemma Get_A_by_F_spec : forall (f:NQ Force) (m:NQ Mass),
      (forall t, NQ2R m t <> 0) ->
      NewtonLaw2_spec f m (Get_A_by_F_M f m).
  Proof.
    intros. unfold NewtonLaw2_spec. intros.
    eapply (NewtonLaw2_Rule f m _). (* ��һ���϶������⣬������� Get_A_by_F_M ��������ʡ�*)
    ?
  Qed.
