(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  v2
  尝试增加 多种数据类型

  备注：
  1. 坚持使用尾递归
  
  参考：
  1. vol4_qc/TImp.v
 *)

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Require Import List. Import ListNotations.
Local Open Scope string.


(** * Type Classes *)

(** ** Show *)

(** 显示接口 *)
Class Show A : Type := {
    show : A -> string
  }.

(** bool 显示实例 *)
Instance showBool : Show bool := {
    show := fun b => if b then "true" else "false"
  }.
Compute (show true).

(** primary 显示实例 *)
Inductive primary := Red | Green | Blue.
Instance showPrimary : Show primary := {
    show :=
      fun c =>
        match c with
        | Red => "Red"
        | Green => "Green"
        | Blue => "Blue"
        end
  }.
Compute (show Blue).

(** nat到字符串 *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d :=
    match n mod 10 with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
    end in
  let acc' := d ++ acc in
  match time with
  | 0 => acc'
  | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n:nat) : string :=
  string_of_nat_aux n n "".

(** nat 显示实例 *)
Instance showNat : Show nat := {
    show := string_of_nat
  }.
Compute (show 125).

(** (nat,bool) 显示实例 *)
Instance showNatBool : Show (nat * bool) := {
    show :=
      fun a =>
        let (n,b) := a in
        "(" ++ show n ++ "," ++ show b ++ ")"
  }.
Compute show (32,true).
Compute show (32,(25,true)). (* 嵌套的话，就不能完美显示 *)

Reset showNatBool.

(** pair 显示实例 *)
Instance showPair {A B} (_:Show A) (_:Show B) : Show (A*B) := {
    show :=
      fun ab =>
        let (a,b) := ab in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Compute show (32,true).
Compute show (32,(25,true)).
Check showPair showNat showBool.

(** 书上给的另一种写法 *)
Instance showPair1 {A B} `{Show A} `{Show B} : Show (A*B) := {
    show :=
      fun ab =>
        let (a,b) := ab in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Check @showPair1 _ _ showNat showBool.


(** 定义统一的 show，显示任何 Show 类别的东西 *)

(** 显示一个值 *)
Definition showOne {A:Type} `{Show A} (a:A) : string :=
  "The value is " ++ show a.
Compute (showOne true).
Compute (showOne 32).
Compute (showOne (32,true)).
Compute (showOne (32,(45,true))).

(** 显示两个值 *)
Definition showTwo {A B:Type} `{Show A} `{Show B} (a:A) (b:B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.
Compute (showTwo true 42).
Compute (showTwo Red Green).

(** ** Eq 布尔相等 *)

(** 布尔相等接口 *)
Class Eq A := {
    eqb : A -> A -> bool;
  }.
Notation "x =? y" := (eqb x y) (at level 70).

(** bool 的布尔相等实例 *)
Instance eqBool : Eq bool := {
    eqb :=
      fun a b => 
        match a,b with
        | true, true | false, false => true
        | _, _ => false
        end
  }.
(** nat 的布尔相等实例 *)
Instance eqNat : Eq nat := {
    eqb := Nat.eqb
  }.

(** 备注：有些类型是不可判定的，例如 nat->nat 上的相等性，因为函数的定义方式
    是无穷的。常见的是，nat 上的相等性是可计算的 *)

(** 练习，bool -> bool 上的布尔相等性成立。
    为什么？定义域是有穷的，枚举所有情况并求and即可
    定义它！*)

(** bool->bool 的布尔相等实例 *)
Instance eqBoolArrowBool : Eq (bool -> bool) := {
    eqb :=
      fun f1 f2 =>
        andb (f1 true =? f2 true) (f1 false =? f2 false)
  }.
Compute eqb negb id.
Compute eqb id id.

(** ** 参数化实例：从旧的Typeclasses产生新的 *)

(** pair 的显示实例（见前文） *)

(** pair 的布尔相等实例 *)
Instance eqPair {A B} {_:Eq A} {_:Eq B} : Eq (A*B) := {
    eqb p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (p1a =? p2a) (p1b =? p2b)
  }.

(** list 的显示实例 *)
Fixpoint showList_aux {A:Type} (s:A->string) (l:list A) (acc:string) : string :=
  match l with
  | [] => acc
  | x :: [] => acc ++ s x
  | x :: l' => showList_aux s l' (acc ++ s x ++ ", ")
  end.

Instance showList {A:Type} {_:Show A} : Show (list A) := {
    show l := "[" ++ showList_aux show l "" ++ "]"
  }.
Compute show [1;2;3;4].

(** list 的布尔相等实例 *)
Fixpoint eqList_aux {A:Type} {_:Eq A} (l1 l2:list A) (acc:bool) : bool :=
  match l1,l2 with
  | [],[] => acc
  | x1 :: l1', x2::l2' => eqList_aux l1' l2' (acc && (eqb x1 x2))
  | _, _ => false
  end.
    
Instance eqList {A:Type} {_:Eq A} : Eq (list A) := {
    eqb l1 l2  := eqList_aux l1 l2 true
  }.
Compute eqb [] [1].
Compute eqb [1;2] [1;1+1].

(** option 的显示实例 *)
Instance showOption {A:Type} {_:Show A} : Show (option A) := {
    show o :=
      match o with
      | None => "!!"
      | Some a => show a
      end
  }.
Compute show (Some 23).
Compute show (None).

(** option 的布尔相等实例 *)
Instance eqOption {A:Type} {_:Eq A} : Eq (option A) := {
    eqb o1 o2 :=
      match o1, o2 with
      | None, None => true
      | Some a1, Some a2 => eqb a1 a2
      | _, _ => false
      end
  }.
Compute eqb (Some 23) (Some 24).
Compute eqb None None.

(** bool->A 的布尔相等实例 *)
Instance eqBoolArrowA {A:Type} {_:Eq A} : Eq (bool -> A) := {
    eqb f1 f2 :=
      eqb (eqb (f1 true) (f2 true)) (eqb (f1 false) (f2 false))
  }.

(** 证明 bool -> bool -> nat 上的布尔相等性 *)
Lemma eqBoolArrowBoolArrowNat : Eq (bool -> bool -> nat).
Proof. apply eqBoolArrowA. Qed.



(** ** Class的层次 *)

(** 也就是说，在一个 Class 之上再构建 Class *)

(** 序关系 接口 *)
Class Ord A {H:Eq A} : Type := {
    le : A -> A -> bool
  }.

(** 有时，Eq 称为 Ord 的 superclass (超类)，但暂时不必要引入 OOP 的概念 *)

(** nat 的序关系实例 *)
Instance natOrd : Ord nat := {
    le := Nat.leb
  }.

(** 可定义Ord之上的 max 函数 *)
Definition max {A:Type} {_:Eq A} {_:Ord A} (x y:A) : A :=
  if le x y then y else x.

(** option 的序关系实例 *)
Instance optionOrd {A} {_:Eq A} {_:Ord A} : Ord (option A) := {
    le :=
      fun o1 o2 =>
        match o1, o2 with
        | None, None => true
        | Some a1, Some a2 => le a1 a2
        | _, _ => false (* 一个存在，另一个不存在，直接返回 *)
        end
  }.

(** pair 的序关系实例 *)
Instance pairOrd {A B} {_:Eq A} {_:Ord A} {_:Eq B} {_:Ord B} : Ord (A*B) := {
    le p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (le p1a p2a) (le p1b p2b)
  }.

Compute le (1,2) (1,3).

(** list 的序关系实例
[] <= []
[1;2] <= [1;3]
[1;2] <= [1;2;3]  即，如果前面都相同时，后者元素多也成立。
[1;2;3] not <= [1;2]
 *)
Fixpoint listOrd_aux {A} {_:Eq A} {_:Ord A} (l1 l2 : list A) (acc:bool) : bool :=
  match l1, l2 with
  | [], [] => acc
  | x1 :: l1', x2 :: l2' => listOrd_aux l1' l2' (andb acc (le x1 x2))
  | [], _ => acc
  | _, [] => false
  end.
    
Instance listOrd {A} {_:Eq A} {_:Ord A} : Ord (list A) := {
    le l1 l2 := listOrd_aux l1 l2 true
  }.

Compute le [] [].
Compute le [] [1;2].
Compute le [1;2] [].
Compute le [1;2] [1;2;3].


(** ** Typeclasses 的工作原理 *)

(**
1. Typeclasses虽然强大，但难以除错，所以要清楚的理解底层机制。
2. 在使用了类型类的类、实例、函数的声明中，记号`{Eq A}的含义，称为 
implicit generation（隐式泛化）。
使用 Generalizable Variables A 可使能该变量。
使用 Generalize Variables All 可使能所有变量，不推荐使用。
3. 记录是积类型。
 *)

Module Record_Playground.

  (* 示例1：*)
  (* 等价于一个单字段的归纳定义，但好处是每个字段有名字 *)
  Record Point :=
    Build_Point {
        px : nat;
        py : nat;
      }.

  Inductive Point' : Set :=
  | Build_Point' : nat -> nat -> Point'.

  (* 记录的语法。而那个 Point' 因为没有字段名称，所以没有这个语法，不是重点 *)
  Check {| px:=2; py:=4 |}.

  (* 访问字段的两种方法 *)
  Definition r : Point := {| px:=2; py:=4 |}.
  Compute (r.(px) + r.(py)).
  Compute (px r + py r).

  (* 记录声明也可以参数化 *)
  Record LabeledPoint (A:Type) :=
    Build_LabeledPoint {
        lx : nat;
        ly : nat;
        lable : A
      }.
  Check {| lx:=2; ly:=4; lable:="Hello" |}.

End Record_Playground.

(** ** Typeclasses 是 Records *)

(** Typeclasses 和 instances，是record类型和值的语法糖，
    只是在证明搜索上有点优势，在类型检查期间可以找到合适的实例 *)

Set Printing All.
Print Show.
(** Variant，是单个字段的记录 *)
Print showNat.
Unset Printing All.

(** 推导实例 *)
Definition eg42 := show 42.
Set Printing Implicit.
Print eg42. (* 自动推导出 @show nat showNat 42 *)
Unset Printing Implicit.
(* 根据通常的类型推导，@show的第二个参数必须是 Show nat 类型的一个值，
   它尝试使用 eauto 证明搜索程序找到或构造这样的一个值，
   参考了一个称为 typeclass_instances 的“提示数据库”。
 *)
Print HintDb typeclass_instances.

(** 使用这个命令，可看到实例推导过程中发生了什么 *)
Set Typeclasses Debug.
Check (show 42).
Check (show (true,42)).
Unset Typeclasses Debug.

(** ** Typeclasses 和 证明 *)

(** 由于Coq中的程序和证明基本上由同样的东西来构成，
    类型类机制平滑的扩展到这些情形，类不仅包含数据和函数，也包含证明。*)

(** 命题的类型类成员 *)

(** 相等可判定接口 *)
Class EqDec (A:Type) {H:Eq A} := {
    eqb_eq : forall x y, x =? y = true <-> x = y
  }.

(** nat 的相等可判定 *)
Instance eqdecNat : EqDec nat := {
    eqb_eq := Nat.eqb_eq
  }.

(** 若手头没有现成的证明，可进入证明模式，并构造一个 *)
Instance eqdecBool' : EqDec bool.
Proof.
  constructor.
  intros x y. destruct x,y; simpl; unfold iff; auto. Defined.

(** 如果环境中有这样的一个类型类示例，如何使用它们来帮助证明 *)
Generalizable Variable A.

Lemma eqb_fact `{EqDec A} : forall (x y z : A),
    x =? y = true -> y =? z = true -> x = z.
Proof.
  intros x y z Exy Eyz.
  rewrite eqb_eq in *. subst. auto. Qed.

(** ** Substructures 子结构，看它是如何用于支持Coq中的大规模证明 *)
(** 类型类实例作为其他类型类成员，称为子结构 *)
From Coq Require Import Relations.Relation_Definitions.

Class Reflexive (A:Type) (R:relation A) := {
    reflexivity : forall x, R x x
  }.
Class Transitive (A:Type) (R:relation A) := {
    transitivity : forall x y z, R x y -> R y z -> R x z
  }.

(** 示例 *)
Generalizable Variables x y z w R.

Lemma tran3 : forall `{Transitive A R}, `{R x y -> R y z -> R z w -> R x w}.
Proof.
  intros.
  apply (transitivity x y w); auto. apply (transitivity y z w); auto. Qed.
  

(** 前序类，是自反类 和 传递类 的子结构 *)
Class PreOrder (A:Type) (R:relation A) := {
    PreOrder_Reflexive :> Reflexive A R;
    PreOrder_Transitive :> Transitive A R
  }.

(** 语法 :> 表示，每个 PreOrder 可以被视为 Reflexive 和 Transitive 关系，
    例如，一个 PreOrder实例，可以立即使用超类上的引理：*)
Lemma tran3_pre : forall `{PreOrder A R}, `{R x y -> R y z -> R z w -> R x w}.
Proof.
  intros.
  apply (transitivity x y w); auto. apply (transitivity y z w); auto. Qed.

(** ** 一些有用的 类型类 *)

(** *** 可判定命题 *)
Require Import ssreflect ssrbool.
Print decidable. (* fun P:Prop => {P} + {~P} : Prop -> Set *)

(** 把“可判定命题”包装成类型类 *)
Class Dec (P:Prop) : Type := {
    dec : decidable P
  }.

(** 现在，可以创建一些示例来编码各种形式的可判定命题，
    例如，在EqDec实例上的x,y值，x = y 是可判定的 *)
Instance decEqDec {A} `{EqDec A} (x y:A) : Dec (x=y).
Proof.
  constructor. hnf. destruct (x=?y) eqn:E.
  - left. rewrite <- eqb_eq; auto.
  - right. rewrite <- eqb_eq. intro. rewrite E in H1. easy. Defined.

(** 类似，还可以提升逻辑操作符上的可判定性 *)
Instance decConj {P Q} {H:Dec P} {I:Dec Q} : Dec (P /\ Q).
Proof.
  constructor. hnf. destruct H as [H], I as [I].
  destruct H,I; auto; right; intro; destruct H; easy. Qed. (* Defined. *)

(** 当 P 和 Q 是可判定命题时，~P 和 P\/ 也是 *)
Instance decNot {P} {H:Dec P} : Dec (~P).
Proof.
  constructor. hnf. destruct H as [H]. destruct H; auto. Defined.

Instance decDisj {P Q} {H:Dec P} {I:Dec Q} : Dec (P \/ Q).
Proof.
  constructor. hnf. destruct H as [H], I as [I].
  destruct H,I; auto; right; intro; destruct H; easy. Defined.

(** 将列表转换到命题，称每个元素都满足某个命题P *)
Fixpoint All {T:Type} (P:T->Prop) (l:list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.

(** 若 P a 对任意 a 是可判定的，建立对于 All P l 的 Dec 实例 *)
Instance decAll {T:Type} (P:T->Prop) {H:forall t, Dec (P t)} (l:list T) : Dec (All P l).
Proof.
  constructor. hnf.
  generalize dependent H.
  generalize dependent P.
  induction l; intros; simpl.
  - left. auto.
  - remember H. clear Heqd. hnf in H. apply IHl in H.
    destruct (d a). destruct dec0,H; auto.
    + right. intros (H1,H2). easy.
    + right. intros (H1,H2). easy.
    + right. intros (H1,H2). easy. Qed. 

(** 一个重要的应用是，可以容易的在布尔和命题之间来回转换，当我们知道是在处理
    可判定命题时。可定义记号 P? 将一个可判定命题 P 转换为 bool *)
Notation "P '?'" :=
  (match (@dec P _) with
   | left _ => true
   | right _ => false
   end)
    (at level 100).

(** 现在，可以将之前要加入布尔操作的东西转换为简洁的命题操作，而仍保留可计算性，
    例如，判断 x,y,z 三个数是否都相等？看看这两种写法，是否后者简洁了很多 *)
Definition eqb_nat3 (x y z:nat) :=
  if andb (x =? y) (andb (y =? z) (x =? z))
  then "all equal"
  else "not all equal".

Definition eqb_nat3' (x y z:nat) :=
  if (x = y /\ y = z /\ x = z)?
  then "all equal"
  else "not all equal".

Compute eqb_nat3 3 4 5.
Compute eqb_nat3' 3 4 5.
(* 注意，上述例子能够成功，依赖于: /\ 提升；nat 提升 等，并且它们都要
   用Defined结束定义，而不是Qed *)

(** * Monad *)

(** 


(** 



(** * 标识符，类型和上下文 *)

(** 标识符 *)
Inductive id :=
| Id : nat -> id
.

(** 尾递归的辅助函数 *)
Fixpoint max_elt_aux (al : list id) last_max_val : nat :=
  match al with
  | [] => last_max_val
  | (Id n') :: al' => max_elt_aux al' (max n' last_max_val)
  end.

(** 计算标识符列表中的最大值 *)
Definition max_elt (al : list id) : nat := max_elt_aux al 0.

(** 测试 *)
Let id_lst1 := [Id 3; Id 2; Id 5].
Compute max_elt id_lst1.

(** 新的Id *)
Definition fresh (al:list id) : id :=
  Id (S (max_elt al)).

(* 测试 *)
Compute fresh id_lst1.

(** Id相等可判定 *)
Lemma id_eqdec (x1 x2:id) : {x1=x2} + {x1<>x2}.
Proof. 
Admitted.

(** 显示 Id *)
Lemma 
Inductive ty :=
| TBool
| TInt8
| TInt32
| TFloat
| TArray
| TStruct
.

    
    |
    |
