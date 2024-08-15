(*
  Purpose   : Learn Canonical Structures
  Author    : Zhengpu Shi
  Date      : May 06, 2023
  
  reference :
  1. https://coq.inria.fr/distrib/current/refman/language/extensions/canonical.html

*)

Require Import Relations.
Require Import EqNat.
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)

(* Structure 应该和 Record 没有区别。
   它们是 Inductive 的特例，限制其不允许递归。*)
Structure Setoid : Type := {
    Carrier :> Set;
    Equal : relation Carrier;
    Equal_equiv : equivalence Carrier Equal
  }.

Definition is_law (A B : Setoid) (f : A -> B) :=
  forall x y : A, Equal _ x y -> Equal _ (f x) (f y).

(* eq_nat 和 @eq nat 有何不同？*)
Print eq_nat.
Goal ~(eq_nat 3 4). simpl. auto. Qed.
Goal ~(3 = 4). intro. inversion H. Qed.
(* 看起来，eq_nat 比 eq 更适合具体数值的证明 *)

(* 一个例子 *)
Axiom eq_nat_equiv : equivalence nat eq_nat.

(* 可直接定义 *)
(* Canonical nat_setoid : Setoid := Build_Setoid eq_nat_equiv. *)

(* 或者先定义，再声明 *)
(* Definition nat_setoid : Setoid := Build_Setoid eq_nat_equiv. *)
(* Canonical nat_setoid. *)

(* 还可以用修饰符来说明(yes/no) *)
#[canonical=yes]
Definition nat_setoid : Setoid := Build_Setoid _ _ eq_nat_equiv.

Lemma is_law_S : is_law _ _ S.
Abort.

(** 查询已有的 Canonical 结构 *)
Print Canonical Projections.
Print Canonical Projections nat.
Print Canonical Projections nat_setoid.
Print Canonical Projections Equal.

(** * 记号重载 *)

(* 为比较谓词构建一个中缀符 ==，将根据项的类型来决定其含义 *)

(* 使用Coq模块作为命名空间，使我们可以用相同的模式和命名惯例。
   为了让例子保持小巧，代数结构EQ.type非常简单，带有一个二元关系的项，并未对此关系
   作任何限制。内部的 theory 模块是重载的记号 ==。
   注意，在实际中，用户可能想要声明 EQ.obj 为 coercion，但我们这里没有这样做。
*)
Module EQ.

  (* 定义规范（操作+性质，这里没有性质） *)
  Record class (T : Type) := Class { cmp : T -> T -> Prop }.

  (* 将基类型和规范绑定在一起，构成一个复合的新类型 *)
  Structure type := Pack { obj : Type; class_of : class obj}.

  (* 在该新类型上定义新的操作，并映射到底层的操作。换言之，将底层操作封装为统一的op *)
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ the_cmp) := e in the_cmp.

  Check op.

  (* 不允许简单的化简 op，也就是不要展开底层的 Pack *)
  Arguments op {e} x y : simpl never.

  Arguments Class {T} cmp.

  (* 这里是需要导出的接口 *)
  Module theory.
    Notation "x == y" := (op x y) (at level 70).
  End theory.
  
End EQ.

(* 导入记号 *)
Import EQ.theory.

(* 测试，当给了EQ class的一个类型 e 时，它的两个对象可以用 == 关联起来 *)
Locate "==".
Check forall (e : EQ.type) (a b : EQ.obj e), a == b.

(* 此时，EQ class 中没有具体类型 *)
Fail Check 3 == 3.

(* 为 nat 装备一个比较关系 *)
Definition nat_eq (x y : nat) := Nat.compare x y = Eq.
(* 建立 EQ class of nat *)
Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.

(* 建立 EQ type of nat。此处，Pack将 nat 作为索引，关联到了 nat_EQcl 这个值上 *)
Canonical Structure nat_EQty : EQ.type := EQ.Pack _ nat_EQcl.

(* Coq现在已经将 == 绑定到了 nat_eq 关系，而且能够做类型检查 *)
Compute 3 == 3.
Compute 3 == 4.

(* 类似的，可以为其他按类型装备比较关系，并使用 == 记号 *)

(** * 派生的 Canonical 结构 *)
(* 来看如何处理类型构造 *)

(* Coq无法比较pair *)
Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) == (a,b).

(* 我们需要告诉Coq *)
Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj e2) :=
  fst x == fst y /\ snd x == snd y.
Definition pair_EQcl e1 e2 := EQ.Class (@pair_eq e1 e2).
Canonical pair_EQty (e1 e2 : EQ.type) : EQ.type :=
  EQ.Pack _ (pair_EQcl e1 e2).

(* 现在可以了 *)
Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) == (a,b).

Check forall n m : nat, (3, 4) == (n, m).

(* 还可以组合更复杂的例子 *)
Check forall (e : EQ.type) (a b : EQ.obj e), ((a,b),a) == ((a,a),b).

(** 哈哈，这里确实很精彩。
    在传统方式下，以 mat 和 vec 为例，如果要实现 (vec0,vec1) == (vec2,vec3)，可能会麻烦。
    但这里看起来可以更加统一的实现，而且是可组合的。
*)

(** * Hierarchy of structures *)

(* 为了一个有趣的例子，我们需要另一个基本 class。我们选择序关系，用 <= 记号 *)
Module LE.
  
  (* 定义规范（操作+性质，这里没有性质） *)
  Record class (T : Type) := Class { cmp : T -> T -> Prop }.

  (* 将基类型和规范绑定在一起，构成一个复合的新类型 *)
  Structure type := Pack { obj : Type; class_of : class obj}.

  (* 在该新类型上定义新的操作，并映射到底层的操作。换言之，将底层操作封装为统一的op *)
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ f) := e in f.

  (* 不允许简单的化简 op，也就是不要展开底层的 Pack *)
  Arguments op {_} x y : simpl never.

  Arguments Class {T} cmp.

  (* 这里是需要导出的接口 *)
  Module theory.
    Notation "x <= y" := (op x y) (at level 70).
  End theory.
  
End LE.

(** 为 nat 注册一个典范的 LE class *)
Import LE.theory.

Definition nat_le x y := Nat.compare x y <> Gt.
Definition nat_LEcl : LE.class nat := LE.Class nat_le.
Canonical Structure nat_LEty : LE.type := LE.Pack _ nat_LEcl.

(* 现在，再为 pair 注册 <= *)
Definition pair_le e1 e2 (x y : LE.obj e1 * LE.obj e2) :=
  fst x <= fst y /\ snd x <= snd y.
Definition pair_LEcl e1 e2 := LE.Class (@pair_le e1 e2).
Canonical pair_LEty (e1 e2 : LE.type) : LE.type := LE.Pack _ (pair_LEcl e1 e2).

(* 现在，有一些有趣的例子了 *)
Check (3,4,5) <= (3,4,5).
Compute (3,4,5) <= (3,4,5).

(* 我们可以把 == 和 <= 用在具体的类型上 *)
Check 2 <= 3 /\ 2 == 2.
(* 但是，我们无法在一个类型上同时装备两个关系来开发代数理论。*)
Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <= x -> x == y.
Fail Check forall (e : LE.type) (x y : LE.obj e), x <= y -> y <= x -> x == y.

(* 需要定义一个新的类，继承自 EQ 和 LE *)
Module LEQ.

  (* 这个minxin组件，包含了所有需要项EQ和LE添加的附加内容，
     这里的 compat 是说要组合的两个关系是相容的*)

  (* 方式1：EQ 来支持 le *)
  Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop) :=
    Mixin { compat : forall x y : EQ.obj e, le x y /\ le y x <-> x == y}.
  
  (* 定义规范（操作+性质，这里有了额外的性质，并且操作不是直接写出来，而是用 class *)
  Record class (T : Type) :=
    Class {
        EQ_class : EQ.class T;
        LE_class : LE.class T;
        extra : mixin (EQ.Pack _ EQ_class) (LE.cmp _ LE_class)
      }.

  (* 将基类型和规范绑定在一起，构成一个复合的新类型 *)
  Structure type :=
    _Pack {
        obj : Type;
        (* 标记为非典范的，使得为实例搜索时无效 *)
        #[canonical=no] class_of : class obj
      }.

  (* 这里新的操作要定义 *)
  (* Definition op (e : type) : obj e -> obj e -> Prop := *)
  (*   let 'Pack (Class f) := e in f. *)

  (* (* 不允许简单的化简 op，也就是不要展开底层的 Pack *) *)
  (* Arguments op {_} x y : simpl never. *)

  Arguments Mixin {e le} _.
  
  Arguments Class {T} _ _ _.

  Module theory.
    (* 不幸的是，仍然有问题 *)
    (* Check forall (e : type) (x y : obj e), x <= y -> y <= x -> x == y. *)

    (* 问题是，两个 class LE 和 LEQ 没有用 subclass 关系关联起来。
       换言之，Coq不知道一个 LEQ class 的对象也是一个 LE class 的对象 *)

    (* 这两个构造告诉Coq如何通过 LEQ.type 典范的构造 LE.type 和 EQ.type *)
    Definition to_EQ (e : type) : EQ.type := EQ.Pack _ (EQ_class _ (class_of e)).
    Definition to_LE (e : type) : LE.type := LE.Pack _ (LE_class _ (class_of e)).
    Canonical to_EQ.
    Canonical to_LE.

    Lemma lele_eq (e : type) (x y : obj e) : x <= y -> y <= x -> x == y.
      intros. apply (compat _ _ (extra _ (class_of e))). split; auto. Qed.

    Arguments lele_eq {e} x y _ _.
  End theory.
  
End LEQ.

Import LEQ.theory.

Check lele_eq.

(* 当然想要在任何代数结构实例上用用这个结果 *)

(* 在 nat 上，失败了 *)
Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
Fail apply (lele_eq n m).
Abort.

(* 在 pair 上，也会失败 *)
Example test_algebraic2 (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
  n <= m -> m <= n -> n == m.
Fail apply (lele_eq n m).
Abort.

(* 问题还是在于，要告诉Coq，nat类型是 LEQ class，以及类型构造器 prod 与 LEQ class 的交互  *)
Lemma nat_LEQ_compat (n m : nat) : n <= m /\ m <= n <-> n == m.
Admitted.

Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.

Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2)
  : n <= m /\ m <= n <-> n == m.
Admitted.

Definition pair_LEQmx l1 l2 := LEQ.Mixin (@pair_LEQ_compat l1 l2).

(* 接下来，要将 nat 和 prod构造器 注册为 LEQ class，
   第一种该方法，非常繁琐。第二种方法会更紧凑 *)
Module Add_instance_attempt.

  Canonical Structure nat_LEQty : LEQ.type :=
    LEQ._Pack _ (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).

  Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
    LEQ._Pack _
      (LEQ.Class
         (pair_EQcl (to_EQ l1) (to_EQ l2))
         (pair_LEcl (to_LE l1) (to_LE l2))
         (LEQ.Mixin (@pair_LEQ_compat l1 l2))).

  Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
  apply (lele_eq n m). Qed.
  
  Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n -> n == m.
  apply (lele_eq n m). Qed.

  (* 上面并没有直接提供 nat * nat 上的直接证明，而是提供了：
     1. n 和 m 是 nat 类型
     2. prod 保持这个性质
     这两个事实的组合，是Coq进行典范结构推断时自动执行证明搜索的简单形式 *)

End Add_instance_attempt.

(* 第二种，紧凑的声明典范结构 *)

(* 需要一些基础设施 （infrastructure） *)
Require Import Strings.String.

Module infrastructure.

  (* 影子类型 *)
  Inductive phantom {T : Type} (t : T) : Type := Phantom.

  Definition unify {T1 T2 : Type} (t1 : T1) (t2 : T2) (s : option string) :=
    phantom t1 -> phantom t2.

  Definition id {T} {t : T} (x : phantom t) := x.

  (* 例如 [find e | EQ.obj e ~ T | "is not an EQ.type"，读作：
     找到一个class e，使得 e 的对象是T类型，或者失败消息"T is not an EQ.type" *)
  Notation "[find v | t1 ~ t2 ] p" :=
    (fun v (_ : unify t1 t2 None) => p)
      (at level 50, v name, only parsing).

  (* 这里是要Coq来解决一个特定的归一化问题，要求Coq推断一些典范结构，看 MT13 的论文 *)
  Notation "[find v | t1 ~ t2 | s ] p" :=
    (fun v (_ : unify t1 t2 (Some s)) => p)
      (at level 50, v name, only parsing).
  
  Notation "'Error : t : s" :=
    (unify _ t (Some s))
      (at level 50, format "''Error' : t : s").
  
  Open Scope string_scope.

End infrastructure.

Import infrastructure.

(* 现在，我们可以开始了 *)

(* Check LEQ.mixin _ _. *)

(* Variable T : Type. *)
(* Variable e0 *)


Definition packager T e0 le0 (m0 : LEQ.mixin e0 le0) :=
  [find e | EQ.obj e ~ T | "is not an EQ.type" ]
  [find o | LE.obj o ~ T | "is not an LE.type" ]
  [find ce | EQ.class_of e ~ ce ]
  [find co | LE.class_of o ~ co ]
  [find m | m ~ m0 | "is not the right mixin" ]
  LEQ._Pack T (LEQ.Class ce co m).

(* 这里，类型 T 是索引，一个 mixin m，它推断所有其他LEQ class的要素，
   并将典范值关联到索引 T。
   总之，对 LEQ class 的唯一要添加的信息就是 mixin，其他对 T 来说都是典范的，可被推断。
   由于 Pack 是一个记号，所以不会在其声明时做类型检查。
   它会在被使用时做检查，使用时，T将会是一个具体类型。
   这里的 _ 和 id 是传递给 packeger 的用于类型推断，而 id 会强制它们做推断。
   细节见 MT13 *)
Notation Pack T m := (packager T _ _ m _ id _ id _ id _ id _ id).

(* 此时，典范实例的声明会很紧凑 *)
Canonical Structure nat_LEQty := Eval hnf in Pack nat nat_LEQmx.
Print nat_LEQty.

Canonical Structure pair_LEQty (l1 l2 : LEQ.type) :=
  Eval hnf in Pack (LEQ.obj l1 * LEQ.obj l2) (pair_LEQmx l1 l2).
Print pair_LEQty.

(* 错误消息会很智能，只要看最后的出错消息 *)
Fail Canonical Structure err := Eval hnf in Pack bool nat_LEQmx.

(* 试试 bool *)
Definition bool_eq (x y : bool) := x = y.
Definition bool_EQcl : EQ.class bool := EQ.Class bool_eq.
Canonical Structure bool_EQty : EQ.type := EQ.Pack _ bool_EQcl.
Fail Canonical Structure err := Eval hnf in Pack bool nat_LEQmx.

(* 最感兴趣的是，这些 [find *** 是如何一步步往下进行的，整个系统行为非常的一致~ *)
