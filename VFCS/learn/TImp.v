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
