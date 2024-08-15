(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix-Valued Function (MVF)
  author    : Zhengpu Shi
  date      : 2024.06
  
  remark    :
  1. 矩阵值函数是 A -> A^{r×c} 类型的函数
     在以下视频中有介绍一些记号和应用
     https://www.youtube.com/watch?v=9_8khxueFlU
     https://www.youtube.com/watch?v=cJlnePo_UzE

  2. `mvf tA r c` is the type of matrix-valued function, it is polymorphic
  3. Regarding "algebraic opertions", we only provide a limited implementation,
     that is, we assume that the elements have a field structure, such as R types.
     For future work, we will develop more detailed theory.
 *)

Require Import VecValFun.
From FinMatrix Require Import Matrix.

Declare Scope MatValFun_scope.
Delimit Scope MatValFun_scope with MVF.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VecValFun_scope.
Open Scope mat_scope.
Open Scope MatValFun_scope.

(** The type of matrix-valued function *)
Definition mvf {tA : Type} (r c : nat) : Type := tA -> @mat tA r c.
Notation smvf n := (mvf n n).

Definition mvftrans {tA r c} (F : @mvf tA r c) : @mvf tA c r := fun t => (F t)\T.
Notation "F \T" := (mvftrans F) : MatValFun_scope.

(* Algebraic operations *)
Section alg.
  Context `{HFiled : Field}.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv a b := (a + -b).
  Infix "/" := Adiv : A_scope.

  Notation madd := (@madd _ Aadd _).
  Notation mopp := (@mopp _ Aopp _).
  Notation mscal := (@mscal _ Amul _).
  Notation mmul := (@mmul _ Aadd 0 Amul _ _ _).
  Notation mmulv := (@mmulv _ Aadd 0 Amul _ _).
  
  Infix "+" := madd : mat_scope.
  Notation "- A" := (mopp A) : mat_scope.
  Notation msub A B := (A + - B).
  Infix "-" := msub : mat_scope.
  Infix "s*" := mscal : mat_scope.
  Infix "*" := mmul : mat_scope.
  Infix "*v" := mmulv : mat_scope.
  
  Notation mvf := (@mvf tA).
  
  (** MVF addition *)
  Definition mvfadd {r c} (A B : mvf r c) : mvf r c := fun t => A t + B t.
  Infix "+" := mvfadd : MatValFun_scope.

  (** MVF opposition *)
  Definition mvfopp {r c} (A : mvf r c) : mvf r c := fun t => - A t.
  Notation "- f" := (vvfopp f) : MatValFun_scope.

  (** MVF scaling *)
  Definition mvfscal {r c} (a : tA) (A : mvf r c) : mvf r c := fun t => a s* A t.
  Infix "s*" := mvfscal : MatValFun_scope.
  
  (** MVF multiplication *)
  Definition mvfmul {r c s} (A : mvf r c) (B : mvf c s) : mvf r s :=
    fun t => A t * B t.
  Infix "*" := mvfmul : MatValFun_scope.
  
  (** MVF matrix multiply vector *)
  Definition mvfmulv {r c} (A : mvf r c) (a : vvf c) : vvf r :=
    fun t => A t *v a t.
  Infix "*v" := mvfmulv : MatValFun_scope.

End alg.
  
(* more operations on mvf over R type *)
Section mvf_R.
  Import MatrixR.

  (** MVF skew3 *)
  Definition mvfskew3 (A : vvf 3) : smvf 3 := fun t => skew3 (A t).

End mvf_R.

Hint Unfold
  mvftrans
  mvfadd mvfopp mvfscal mvfmul mvfmulv
  mvfskew3
  : mvf.
