(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : 有理式
  author      : Zhengpu Shi
  date        : 2022.08
  
  ref         :
  1. https://zh.wikipedia.org/wiki/多项式
  2. https://baike.baidu.com/item/整式/5961855
  
  remark      :
  1. 如何表达 代数式、有理式、整式、分式、多项式、单项式？
  2. 不同数域上对多项式进行因式分解
  3. 分式的真分式化
  4. 待定系数法
  5. 留数法
*)

Require Export FuncExt.


(** 代数表达式作用域 *)
Declare Scope AE_scope.
Delimit Scope AE_scope with AE.
Open Scope AE_scope.

(** 代数表达式 *)
Module Import AlgebraicExpression.
  Context {P : Type}.

  (** 在数域 P 上的代数表达式 *)
  Inductive Aexp :=
  | Acnst (p : P)           (* 常量 *)
  | Avar (n : nat)          (* 变量 *)
  | Aadd (e1 e2 : Aexp) | Aopp (e : Aexp)
  | Amul (e1 e2 : Aexp) | Ainv (e : Aexp)
  .
  
  Coercion Acnst : P >-> Aexp.
  
  (** 乘方运算 *)
  Definition powern (x : Aexp) (n : nat) : Aexp :=
    nexec x (fun y => Amul y x) n.

End AlgebraicExpression.

(* Check (Acnst 3) : Aexp.
Check (Acnst 3) : Aexp.


(** 记号 *)
Infix "+" := Aadd : AE_scope.
Notation "- e" := (Aopp e) : AE_scope.
Infix "*" := Amul : AE_scope.
Notation "/ e" := (Ainv e) : AE_scope.
Notation "# n" := (Avar n) (at level 10) : AE_scope.



Check #1 * #2.

Section example.
  Let NatNorminal := @Norminal nat.
  Definition Nval_nat (p : nat) := Nval p.
  Coercion Nval_nat : nat >-> Norminal.
  Check ( 3 ) * 4.
  Locate "(".
  Check (3) : Norminal.
  
  Check 3 * 4.
  Check Nvar.
Coercion Nval : ?P >-> Norminal. 
  Let 
End example.


Definition Norminal := Item. *)
