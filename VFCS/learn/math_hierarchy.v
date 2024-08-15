(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose       : learn Math Hierarchy
  
  参考：
  1. vol4_qc/Typeclasses.v
 *)

Set Warnings "-deprecated-instance-without-locality".

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
Require Import List. Import ListNotations.
Local Open Scope string.


(** * Mathematical Hierarchy *)

(** ** Monoid *)

Class Monoid (A:Type) (Aop:A->A->A) : Type := {
    assoc : forall x y z, Aop x (Aop y z) = Aop (Aop x y) z;
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

(** *** 可判定（真假）的命题 *)
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

Compute 3 = 4.
Compute 3 = 4?. (* 依赖于 Dec 类型类，以及 nat 上做了实例化，还有 ? 记号 *)

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

(** 在 Haskell 中，typeclasses 用的很多的一个地方是 Monad typeclass，
    特别是在为了单子操作而与Haskell的 “do 记号” 合起来。
    
    Monad是在很多情形下组织和简化编程的非常强大的工具，当计算可被看做是
    生成一个结果时附带有某种“效应”时。可能的例子包括：
        输入、输出；
        状态突变；
        失败；
        非终止；
        随机
    在网上有很多关于在Haskell中单子编程的好的教程。
    从来没有见过monad的读者可能想要参考其中的某个来完全理解这里的例子。

    在Coq中，monad也被大量使用，但由于typeclasses是相对最近加入Coq的事实，
    以及Coq的记号扩展机制允许用户为特定情形定义do记号的变体的事实，
    这导致了monad定义的泛滥：很多旧的项目只是定义它们自己的单子和一元记号——
    有的基于typeclass，大多都不是——而新的项目使用这些单子泛型库的其中一个。
    我们当前最喜欢的（2017年夏天）是 Gregory Malecha's ext-lib 中的
    monad typeclasses。
    https://github.com/coq-community/coq-ext-lib/blob/master/theories/
    Structures/Monad.

    自行安装，比如通过 opam
 *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

(** 这个库的主要定义是以下的 typeclass *)
Module Monad_Playground.

  (** 一个类型簇M是Monad类的实例，若我们能定义出 ret 和 bind 函数。*)
  Class Monad (M : Type -> Type) : Type :=
    Build_Monad {
        ret : forall {T:Type}, T -> M T;
        bind : forall {T U:Type}, M T -> (T -> M U) -> M U
      }.
  
End Monad_Playground.


(** 例如，我们可以为 option 单子实例 *)
Instance optionMonad : Monad option := {
    ret T x := Some x;
    bind T U m f :=
      match m with
      | None => None
      | Some x => f x
      end
  }.

(** 从 Monad 库得到的一个很好的东西是为 bind 的轻量化记号。

    比如，
    1. 用 x <- m1;; m2 代替 bind m1 (fun x => m2)
    2. 对于m1的返回值x，若m2不需要，则
       可用 m1 ;; m2 代替 bind m1 (fun _ => m2)
    3. 这会让我们写出关于 "option plumbing" 的很紧凑的程序。
 *)

(** 例如，从列表找出 n-th 元素，若元素数量不够，返回 None *)

Fixpoint nth_opt {A:Type} (n:nat) (l:list A) : option A :=
  match l with
  | [] => None
  | h::t =>
      if n =? 0
      then Some h
      else nth_opt (n-1) t
  end.

(** 写一个函数来求和列表中的前三个元素（如果列表太短返回None）*)
Definition sum3 (l:list nat) : option nat :=
  x0 <- nth_opt 0 l;;
  x1 <- nth_opt 1 l;;
  x2 <- nth_opt 2 l;;
  ret (x0+x1+x2).

(** 哇，确实方便了不少，看起来“再也不用处理这类简单的option错误了”，
    因为，一旦错误一次就立即返回，否则才会往下执行 *)

Compute sum3 [1;2;3].
Compute sum3 [1;2].

(** 使用monad编程的另一个便利是：一系列“lifting”操作符，
    从普通值上的函数到monadic computation函数。
    ExtLib 定义了三个：一元；二元；三元的。定义看起来如下：*)
Definition listM {m:Type->Type} {_:Monad m} {T U:Type} (f:T->U)
  : m T -> m U :=
  fun x => bind x (fun x => ret (f x)).

Definition listM2 {m:Type->Type} {_:Monad m} {T U V:Type} (f:T->U->V)
  : m T -> m U -> m V :=
  fun x y => bind x (fun x => liftM (f x) y).
  
Definition listM3 {m:Type->Type} {_:Monad m} {T U V W:Type} (f:T->U->V->W)
  : m T -> m U -> m V -> m W :=
  fun x y z => bind x (fun x => liftM2 (f x) y z).
    
(** 例如，有两个 option nat，想要计算和 *)
Definition sum3opt (n1 n2 : option nat) :=
  x1 <- n1;;
  x2 <- n2;;
  ret (x1 + x2).
(** 可以使用 listM2 写出更紧凑的形式 *)
Definition sum3opt' (n1 n2 : option nat) :=
  listM2 plus n1 n2.

(** 在 ExtLib 库的 /examples 目录下有更多例子 *)

(** ** 其他 *)

(** Coq标准库中的两个流行的类型类是：Equivalence（相关的类是 Reflexive,
    Transitive, etc.) 和 Proper. 参考 "A Gentle Introduction to Type Classes
    and Relations in Coq" 论文。
    关于 typeclasses 的更大的集合，用于形式化数学，在 "Type Classes for 
    Mathematics in Type Theory" 论文。*)

(** * 控制实例化 *)

(** ** 默认 *)
Check @eqb.

Definition foo x := if x =? x then "Yes" else "no".
Check foo. (* 类型是 (bool -> bool) -> string *)
(* 这很奇怪。由于 =? 导致需要 Eq，这说明 实例化会对搜索引擎有影响。*)

(** 练习，使用 Set Typeclasses Debug 来排除 *)
Set Typeclasses Debug.

Check (foo negb).
Fail Check (foo true).

Unset Typeclasses Debug.
(* 我没有完成这个练习，不知怎么做 *)

(** 当有多个实例时，Coq并没有检查 overlap，会“随机”选择一个。
    可手动处理这种交叠，通过增、删 hint 数据库。*)
Inductive baz := Baz : nat -> baz.

Definition show_baz_prefix (b:baz) (prefix:string) :=
  match b with Baz n => prefix ++ ": " ++ show n end.

Instance baz1 : Show baz := { show b := show_baz_prefix b "1" }.
Instance baz2 : Show baz := { show b := show_baz_prefix b "2" }.
Definition baz3 : Show baz.
  constructor; intros b; apply (show_baz_prefix b "3"). Qed.
Definition baz4 : Show baz.
  constructor; intros b; apply (show_baz_prefix b "4"). Defined.

Compute (show (Baz 32)). (* Coq随机选择了一个实例 *)

(** 删除提示 *)
Remove Hints baz2 : typeclass_instances.
Compute (show (Baz 32)).
Remove Hints baz1 : typeclass_instances.
Compute (show (Baz 32)).

(** 添加删除掉的提示，或原本不是由 Instance声明，而它又具有正确的类型时 *)
Existing Instance baz4.
Compute (show (Baz 32)).

(** 控制在证明搜索中要使用哪个实例的另一种方法是：
    指定交叠实例的优先级 *)
Instance baz10 : Show baz | 0 := { show b := show_baz_prefix b "10" }.
Compute (show (Baz 32)).
(** 0的优先级最高。默认的优先级应该至少是1开始，并且按如下原则：
    默认值是：实例中binders的数量（也就是，更具体——越少多态——的实例会优先）*)

(** 添加实例时也可指定优先级 *)
Existing Instance baz4 | 0.
Compute (show (Baz 32)).  (* 再指定一个 0，则优先于之前设置为优先级0的情形 *)

Existing Instance baz1 | 0.
Compute (show (Baz 32)).  (* 再指定一个 0，则优先于之前设置为优先级0的情形 *)
(* 换言之，相同级别下，最后指定的最优先 *)

(** * 调试 *)

(** ** 实例化失败 *)

(** 使用 typeclasses 的一个缺点，尤其是同时有很多 typeclases 时，
    出错信息会很令人费解 *)

(** 一些简单的情形 *)
Inductive bar := Bar : nat -> bar.
Fail Definition eqBar := (Bar 42) =? (Bar 43).
Fail Definition ordBarList := le [Bar 42] [Bar 43].
(** 这些例子很清晰的说明了问题。 *)

(** 但是，复杂的情形下，可能很难。
一些简单的技巧可能有用：
1. Set Printing Implict，并用 Check, Print 来检查出错处的表达式类型。
2. 使用 @注解 并显式为自动实例化的地方填充参数，检查是否按照你的理解实例化了。
3. 用 Set Typeclasses Debug 来打开示例搜索的跟踪。
完整形式是 Set Typeclasses Debug Verbosity x.
这里的x是1或2，默认是1，指定2的话会打印更多信息。*)

(** 一个带有错误消息的可能的困扰是，当你忘了 `记号。例如：*)
Fail Definition max {A:Type} {Ord A} (x y:A) : A :=
  if le x y then y else x.

(** ** 不终止 *)

(** 类型类实例化会出错的另一种更烦人的方式是：发散。*)

(** 例子：声明一个具有两个类型参数A和B的类型类 *)
Class MyMap (A B : Type) : Type := { mymap : A -> B }.

(** 声明 bool -> nat 的实例 *)
Instance MyMap1 : MyMap bool nat := { mymap b := if b then 0 else 32 }.
(** 声明 nat -> string 的实例 *)
Instance MyMap2 : MyMap nat string := {
    mymap n := if le n 20 then "small" else "big" }.

Definition e1 := mymap true.
Compute e1.
Definition e2 := mymap 42.
Compute e2.

(** 但是，bool -> string 并不会自动生成。
    虽然这个例子中是确定的，而广泛的例子中，由于中间状态 nat 是无穷，应该
    不是一个确定的问题 *)
Fail Definition e3 : string := mymap false.

(** 修复：可以定义能够合并“A->B的实例”和“B->C的实例”的泛型实例 *)
Instance MyMap_trans {A B C:Type} {_:MyMap A B} {_:MyMap B C} : MyMap A C :=
  { mymap a := mymap (mymap a) }.

Definition e3 : string := mymap false.
Compute e3.

(** 然后，尽管这个例子能工作，实际上还很危险：如果恰巧要求的一个实例不存在，
    则搜索过程会发散（宕机）"C-c C-c"来终止 *)
(* Definition e4 : list nat := mymap false. *)

(** 练习：调试出错信息 *)
Set Typeclasses Debug Verbosity 2.
(* Definition e4 : list nat := mymap false. *)
Unset Typeclasses Debug.

(** * 替代的结构化机制 *)

(** Typeclasses 只是能在Coq中用来结构化大型开发的多种机制之一。其他包括：
    canonical structures
    bare dependent records
    modules and functors
作者提供了两个文献，1个网址。 *)

(** * 来自专家的建议 *)

(** Matthieu Sozeau:
类型类解析是基于无限制的搜索，这是好事也是坏事。
只有证明搜索失败时才返回错误，通常你需要查看解析步骤追踪来找到问题，在最糟的情况下，
搜索会发散。...

*)
