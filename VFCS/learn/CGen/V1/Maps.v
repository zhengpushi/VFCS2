(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.
 *)

(** * Maps: Total Maps or Partial Maps *)

(** 映射（或字典）是普遍存在的数据结构，尤其是在编程语言理论中。
  这里将定义两种风格的映射：
    全映射，包含一个默认值，用于当查找的键不存在时返回该默认值；
    部分映射，返回option类型，键不存在时返回None。*)


(* ################################################################# *)
(** * The Coq Standard Library *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(** Documentation for the standard library can be found at
    https://coq.inria.fr/library/. *)

(* ################################################################# *)
(** * Identifiers 标识符 *)

(** 在映射中用于索引的键的类型。
  在 Lists.v 中使用 [id] 类型，这里使用 string 类型 *)

(** 为比较字符串，定义了函数 [eqb_string]，内部会使用标准库提供的 [string_dec] *)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(** 理解 [string_dec]，它并不返回 [bool]，而是返回 [sumbool]，可认为是带有证明的bool。
  形式的，一个 [{x = y} + {x <> y}] 类型的元素，要么是 [x] 和 [y] 相等的证明，要么是
  它们不相等的证明。在效果上，可以当做 [bool] 来使用。*)

(** 关于字符串相等的一些基本性质 *)
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

(** 两个字符串按照 [eqb_string] 相等，当且仅当，它们按照 [=] 相等。
  所以，[=] 被反射到 [eqb_string] *)
Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
  - rewrite Hs_eq. split. reflexivity. reflexivity.
  - split.
    + intros contra. discriminate contra.
    + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.

(** 同理，不相等的反射。 *)
Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** 一个推论 *)
Theorem false_eqb_string : forall x y : string,
  x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Total Maps 全映射 *)

(** 主要任务是建立部分映射的定义，以及有关它的行为的引理。
  使用函数，而不是键值对的list，这种表示的好处是，它提供了映射的更外延性的视图。
  如果对两个映射的查询响应相同，则它们将被表示为完全相同的函数，而不仅仅是“等价”的函数。
  因此，使用映射会简化证明。*)

(** 构造部分映射分两步。第一步，建立全映射。*)

Definition total_map (A : Type) := string -> A.

(** 直觉上，一个类型A上的全映射只是一个函数，能被用于查找字符串返回A。*)

(** 函数 [t_empty] 返回空的全映射，需要一个默认值，任何输入都返回该默认值。*)
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** [update] 函数，需要一个映射m、一个键x和一个值v，返回新的映射，
  该映射把x对应到v，其余任何键都由m来负责处理。*)
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(** 这个定义是典型的高阶编程的例子，该函数接收一个函数 m，返回一个新的函数，
  返回的函数具有所期望的映射的行为。 *)

(** 示例 *)
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(* Compute examplemap "abc".
Compute examplemap "foo".
Compute examplemap "bar".
 *)

(** 一些记号 *)

(** 空的全映射 *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** 更新全映射 *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** 为了后续使用，一些基本的性质如下。*)

(** 一些证明需要函数外延性(functional extensionality)公理 *)

(** 空映射对所有输入返回默认值 *)
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. intros. auto. Qed.

(** 先将(x,v)写入m，再用x访问m，得到v *)
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. intros. unfold t_update. rewrite <- eqb_string_refl. auto. Qed.

(** 先将(x1,v)写入m，再用x2访问m，得到的结果与未更新m前得到的结果相同。 *)
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof. intros. unfold t_update. apply eqb_string_false_iff in H. rewrite H.
  auto. Qed.

(** 先将(x,v1)写入m，再将(x,v2)写入m，等同于只将(x,v2)写入m。*)
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof. intros. apply functional_extensionality. intros.
  unfold t_update. destruct (string_dec x x0) as [H | H].
  - subst. rewrite <- eqb_string_refl. auto.
  - apply eqb_string_false_iff in H. rewrite H. auto.
Qed.

(** 字符串相等的反射 *)
Lemma eqb_stringP : forall x y : string,
  reflect (x = y) (eqb_string x y).
Proof. intros. destruct (string_dec x y) as [H | H].
  - subst. rewrite <- eqb_string_refl. constructor. auto.
  - apply eqb_string_false_iff in H. rewrite H. constructor.
    apply eqb_string_false_iff. auto.
Qed.

(** 现在，任给出两个字符串 x1,x2，可使用策略 [destruct (eqb_stringP x1 x2)] 来
  进行分情况分析，并生成关于 x1 和 x2 相等的假设。 *)

(** 用 [eqb_stringP] 证明如下定理：
  若用键x和一个映射m中已有的值来更新该映射，其结果还是该映射。*)
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros. 
  apply functional_extensionality; intros.
(*   destruct (eqb_stringP x x0). *)
  destruct (string_dec x x0).
   unfold t_update; apply functional_extensionality; intros.
  
  destruct (string_dec x x0). subst.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute)

    Use [eqb_stringP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Partial maps *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

(** Finally, for partial maps we introduce a notion of map inclusion,
    stating that one map includes another:  *)

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

(** We then show that map update preserves map inclusion, that is: *)

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A)
                                (x : string) (vx : A),
  inclusion m m' ->
  inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold inclusion.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_stringP x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.

(** This property is very useful for reasoning about languages with
    variable binding, such as the Simply Typed Lambda Calculus that we
    will see in _Programming Language Foundations_, where maps are
    used to keep track of which program variables are defined at a
    given point. *)

(* 2021-08-11 15:08 *)
