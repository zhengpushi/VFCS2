(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 带有验证和代码生成的层次化模块机制 - 原型
  date      : 2022.09.08
  author    : Zhengpu Shi
  
  整体思路：
  1. 建立类似于Simulink的层次化模块机制。
  2. 模块包含输入、输出和功能三部分，对应于一个数学函数，也对应于一段程序代码。
  3. 使用IMP语言来编写和验证程序，并且使用打印将AST转换为C程序字符串。
  4. 新的挑战
    a. 增强IMP，支持更多数据类型
    b. 支持数组及矩阵
    c. 支持函数
    d. 模块化机制
    e. 支持结构体
  
  C子集的定义
  1. 数据类型
  2. 表达式
  
*)

Require Import String.

(** * 数据类型 *)
Inductive DataType :=
| DT_bool | DT_int | DT_char
(* | DT_u8 | DT_u32 | DT_i8 | dt_i32 *)
(* | DT_float | DT_double *)
.

(** * 表达式 *)
Inductive exp 

Inductive aexp {A:Type} :=
| AEcnst 
(** * IMP语言 *)

(** * 模块 *)
