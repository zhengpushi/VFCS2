(*
 Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : C code generation (version 2)
  author      : Zhengpu Shi
  date        : 2022.09.16

  remark      :
  1. 实数表达式的AST、求值、字符串生成。
*)

Require Import List. Import ListNotations.
Require Import Nat.
Require Import StrExt.
Require Import RExt.
Open Scope string_scope.

(* 语法 *)

(** 首先是实数表达式的AST *)

Inductive op1 :=
(* | op1_ropp *)
(* | op1_rinv *)
| op1_fun : string -> op1
.

Definition op1_fun_db : list (string * (R->R)) :=
  [("sin", sin); ("cos", cos); ("sqrt", sqrt)].
Definition op1_fun_def : string * (R->R) := ("def1", fun x => R0).

Inductive op2 :=
| op2_rplus
| op2_rminus
| op2_rmult
| op2_rdiv
| op2_fun : string -> op2.

Definition op2_fun_db : list (string * (R->R->R)) :=
  [("plus", Rplus); ("minus", Rminus)].
Definition op2_fun_def : string * (R->R->R) := ("def2", fun x y => R0).

Fixpoint alst_lookup {A} (l:list (string * A)) (key:string) : option A :=
  match l with
  | (k,v) :: tl => if String.eqb k key then Some v else alst_lookup tl key
  | [] => None
  end.

Inductive aexp :=
| rvar : string -> aexp
| rconst : R -> aexp
| rpow : aexp -> nat -> aexp
| runary : op1 -> aexp -> aexp
| rbinary : op2 -> aexp -> aexp -> aexp.

(* 语义 *)
Fixpoint aeval (a : aexp) (ctx : string -> R) : R :=
  match a with
  | rvar x => ctx x
  | rconst r => r
  | rpow a1 n => pow (aeval a1 ctx) n
  | runary op1 a1 =>
      match op1 with
      (* | op1_ropp => - (aeval a1 ctx) *)
      (* | op1_rinv => / (aeval a1 ctx) *)
      | op1_fun x =>
          match alst_lookup op1_fun_db x with
          | Some op => op (aeval a1 ctx)
          | None => (snd op1_fun_def) (aeval a1 ctx)
          end
      end
  | rbinary op2 a1 a2 =>
      match op2 with
      | op2_rplus => (aeval a1 ctx) + (aeval a2 ctx)
      | op2_rminus => (aeval a1 ctx) - (aeval a2 ctx)
      | op2_rmult => (aeval a1 ctx) * (aeval a2 ctx)
      | op2_rdiv => (aeval a1 ctx) / (aeval a2 ctx)
      | op2_fun x => 
          match alst_lookup op2_fun_db x with
          | Some op => op (aeval a1 ctx) (aeval a2 ctx)
          | None => (snd op2_fun_def) (aeval a1 ctx) (aeval a2 ctx)
          end
      end
  end.

(* C表达式 *)
Section cgen.
  
  Variable R2str : R -> string.

  Fixpoint a2str (a : aexp) : string :=
    match a with
    | rvar x => " " ++ x ++ " "
    | rconst r => " " ++ R2str r ++ " "
    | rpow a1 n => "(" ++ a2str a1 ++ ")^" ++ (nat2str n)
    | runary op1 a1 =>
        match op1 with
        (* | op1_ropp => "- (" ++ (a2str a1) ++ ")" *)
        (* | op1_rinv => "/ (" ++ (a2str a1) ++ ")" *)
        | op1_fun x =>
            let x' : string :=
              match alst_lookup op1_fun_db x with
              | Some _ => x | None => (fst op2_fun_def)
              end in
            x' ++ "(" ++ (a2str a1) ++ ")"
        end
    | rbinary op2 a1 a2 =>
        match op2 with
        | op2_rplus => (a2str a1) ++ "+" ++ (a2str a2)
        | op2_rminus => (a2str a1) ++ "- (" ++ (a2str a2) ++ ")"
        | op2_rmult => (a2str a1) ++ "* (" ++ (a2str a2) ++ ")"
        | op2_rdiv => (a2str a1) ++ "/ (" ++ (a2str a2) ++ ")"
        | op2_fun x => 
            let x' : string :=
              match alst_lookup op2_fun_db x with
              | Some _ => x | None => (fst op2_fun_def)
              end in
            x' ++ "(" ++ (a2str a1) ++ ", " ++ (a2str a1) ++ ")"
        end
    end.
End cgen.

(** 语法助记符 *)
Declare Custom Entry aexp.

Notation "<{ e }>" := e (e custom aexp at level 99).
Notation "( x )" := x (in custom aexp, x at level 99).
Notation "x" := x (in custom aexp at level 0, x constr at level 0).
(* Notation "- x" := (runary op1_ropp x) (in custom aexp at level 1, left associativity). *)
(* Notation "/ x" := (runary op1_rinv x) (in custom aexp at level 1, left associativity). *)
Notation "'\F' op x" := (runary (op1_fun op) x) (in custom aexp at level 5, right associativity).
Notation "x + y" := (rbinary op2_rplus x y) (in custom aexp at level 10, left associativity).
Notation "x - y" := (rbinary op2_rminus x y) (in custom aexp at level 10, left associativity).
Notation "x * y" := (rbinary op2_rmult x y) (in custom aexp at level 4, left associativity).
Notation "x / y" := (rbinary op2_rdiv x y) (in custom aexp at level 4, left associativity).
Notation "op x y" := (rbinary op2_fun op x y) (in custom aexp at level 1, left associativity).
Notation "{ x }" := x (in custom aexp at level 1, x constr).
Coercion rvar : string >-> aexp.
Coercion rconst : R >-> aexp.

(** 一些方便的操作  *)
Definition OP1 (op:string) : aexp->aexp := runary (op1_fun op).
Definition OP2 (op:string) : aexp->aexp->aexp := rbinary (op2_fun op).

Compute OP1 "sin".

(* Definition x : string := "x". *)
(* Definition y : string := "y". *)
(* Definition z : string := "z". *)

(* Hint Unfold x : core. *)
(* Hint Unfold y : core. *)
(* Hint Unfold z : core. *)


(* 示例1 *)
Section test.
  (* 给出表达式的AST  *)
  Let ex1 : aexp := <{"x" + R0 + "y"*"z"*R1 }>.
  Print ex1.

  (* 验证数学性质 *)
  Let ex1_spec : forall ctx,
      let x := ctx "x" in
      let y := ctx "y" in
      let z := ctx "z" in
      aeval ex1 ctx = (x + y * z)%R.
  Proof. intros. cbv. ring. Qed.

  (* 实数到字符串的转换 *)
  Let R2str (r:R) : string :=
        if (r =? R0)%R then "R0"
        else if (r =? R1)%R then "R1"
             else "0000".
  Let R2str' (r:R) : string := "0000".
  
  (* 代码生成 *)
  Open Scope string_scope.
  Compute a2str R2str ex1.      (* 是否可以用Ltac或Coq插件将R常量表达式转换为字符串？ *)
  Compute a2str R2str' ex1.     (* 遗留问题，要想办法处理掉实数的表示问题  *)
End test.

(* 示例2 *)
Section test.

  (* 飞控QQ (4.25)
     N = 60 * sqrt (T / (rho * D_p^4 * C_T))
     M = rho * D_p^t * C_M * (N/60)^2
   *)

  Let T := "T".
  Let rho := "rho".
  Let D_p := "D_p".
  Let C_T := "C_T".
  Let C_M := "C_M".

  (* 公式1: N *)
  Section formula1. 

    (* 定义表达式的AST *)
    Let N : aexp :=
          let f1 := <{ T / (rho * {rpow D_p 4} * C_T) }> in
          <{60 * {OP1 "sqrt" f1}}>.
    Compute aeval N.            (* 这里展开了 sqrt，所以看起来复杂 *)
    Opaque sqrt. Eval cbv in aeval N. (* 当不展开 sqrt 时，表达式会简洁一些 *)

    (* 校验数学性质（防止AST出错，得到其数学表达式） *)
    Let N_spec : forall ctx,
        let vT := ctx T in
        let vrho := ctx rho in
        let vD_p := ctx D_p in
        let vC_T := ctx C_T in
        let vC_M := ctx C_M in
        aeval N ctx = 60 * sqrt (vT / (vrho * vD_p ^ 4 * vC_T)).
    Proof. intros. cbv. ring. Qed.

    (* 生成C代码 *)
    Compute a2str (fun _ => "0000") N. (* 同样是实数表示问题 *)
  End formula1.
End test.
