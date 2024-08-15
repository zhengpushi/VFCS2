(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : 数据类型等各种基础设施
  date        : 2022.09.11
  author      : Zhengpu Shi
  
  remark      :
  1. 模块有多个输入、输出端口。
  2. 每个端口有给定的数据类型。
  3. 数据类型有：标量(还可细分整型、浮点等）、向量、矩阵
  4. 每个模块内部有自己的配置参数（可以是结构体等），但是端口的数据类型就上面这些。
  5. 端口互联，需要保证同类型的输入、输出端口能够连接。
  6. 每个模块携带程序和证明，程序是从输入到输出的函数，证明是输入和输出满足某种关系。
  7. 一个综合器，将各个模块内部的程序取出并合并，以及优化。
*)

Require Import List.
Import ListNotations.

(** 以下，用于证明 *)
Require Import ZArith.
Require Import Reals.
(** 以下，用于代码生成 *)
Require Import Int31.
Require Import Int63.
(* 上面的数据类型应当对应起来 *)

Open Scope R.

(* Print Int31.
Print Int63.
Print digits31.
Print digits.
 *)


Inductive ScalarType :=
| STint (v : nat)
| STfloat (v : R)
.

Inductive Datatype :=
| DTscalar (base : ScalarType)
| DTvector (base : ScalarType) (n : nat)
| DTmatrix (base : ScalarType) (r c : nat)
.

Variable program : list Datatype -> list Datatype.

Record Block := {
  Bin : list Datatype;
  Bout : list Datatype;
  (* 每个输出端口对应一个程序，根据所有的输入得到这一路输出，各路输出互不影响 *)
  Bporgram : list (list Datatype -> Datatype)
}.


Example b1 := Build_Block [DTscalar (STint 3)] [DTscalar (STint 3)] [].
Example b2 := Build_Block [DTscalar (STint 4)] [DTscalar (STint 5)] [].
Example b3 := Build_Block [DTscalar (STint 4)] [DTscalar (STfloat 5)] [].

Check Bin b1.
Check Bout b2.

(**
  o1 = f1();
  o2 = f2(o1);
  o3 = f3();
  o4 = f4(o2,o3);
  f5(o4);   // main loop
*)


