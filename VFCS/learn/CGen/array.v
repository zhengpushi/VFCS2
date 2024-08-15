(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


 Coq中数组一定要建模为依赖类型吗？
*)

(** 映射，除了 map 模型，还可以用 list (id * A) 的方式。
参考 SF_4_qc_TImp。

这个例子非常好，
将 list 版的 map 用在了不同数据类型上，
有希望包装 数组、结构体 等。

在下文 Well-Typed Programs，看起来与 Imp 很像，
但有一点改进，原本 var 是用 string 编码，这里用 id (就是 nat)，
那么效率会快很多，应该是。
也许全局环境变量、局部上下文(多个)，这样有好几套 map。
对结果 result 也做了归纳定义
Inductive result :=
| Success : state -> result
| Fail (* 比如表达式构造错误, true + 1 就会错误。
| OutOfGas  (* 求值时发散的，比如100步内仍无法结束 *)
.
*)

(** 构造性实现，方便证明 *)
Section array.

  Variable A : Type.

  Record array := {
    ALen : nat;
    Adata : nat -> A
  }.

End array.

(** AST，方便代码生成 *)
Module Array_ImpStyle.

  (** 在命令式语言中，数组有关的操作有：
    创建、取数据、修改数据、销毁
    
  *)
  
  (** 那么，将来的代码还需要内存 malloc/free 等操作，
  这里只需要管理内存块的垃圾回收机制 *)
  
  (** 函数内部的局部变量在栈（heap）上，由编译器负责回收。
  全局变量不需要回收，常驻内存。
  是否允许动态申请数组内？
  内存模型中有一个堆区（stack），用户是可以申请的
  
  嵌入式系统的堆的模型很清晰，可以在Coq中建立。
  而且，由于C语言堆上的数据是由程序员维护的，所以我们可以做这样的事情。
  
  把堆建立为字节构成的一个区域，只是没有确定的地址，
  我们只关心占用了多少空间。
  程序调用、中断执行所占用的栈上的情况暂不建立模型。
  *)
  
  Module StackModel.
    
    (** 在Stack上，我们只关心能否找到这些数据，以及使用了多少数据，
    用指针来管理他们即可 *)
    
    (* 内存块，将来要扩充属性，至少包含大小和引用的位置 *)
    Parameter memBlock : Type.
    
(*     Parameter malloc (unitSize : nat) (unitCnt : nat) : memBlock. *)
    Parameter malloc : nat -> nat -> memBlock.
  
  
  End StackModel.

End Array_ImpStyle.



(** 在 SF_3_VFA 中 ADT 这一章，
有 Vectors 的一种做法 *)

Require Import List.
Import ListNotations.

Definition vector (X : Type) := { '(xs,n) : list X * nat | length xs = n }.

Example a_vector : vector nat.
Proof.
  exists ([1],1). auto.
Qed.

Example  econstructor. pose ([2],1). apply p. pose (([1],1)).
