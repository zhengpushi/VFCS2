(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.


  设计一种机制，可以将 Coq模型 和 C代码绑定起来，
  容易的从Coq模型生成 C代码。
  1. 利用 ModuleSig 技术，设计出类似于 Simulink 中的模块，
    对应于C语言中的代码片段（目前先手写，后续可自动生成和优化）
*)

Require Import List.
        Import ListNotations.

Require Import Bool.
Require Import Nat.
Require Import ZArith.
Require Import Reals.
Require Import Ascii String.

Open Scope char.
Open Scope string.
Open Scope R.

(** 布尔表达式AST *)
Inductive bexp :=
| BETrue
| BEFalse
| BEConst (_ : bool)
| BEVar (_ : string)
| BENot (_ : bexp)
| BEAnd (_ _ : bexp)
.

(** AST到Coq类型 *)
Fixpoint bexp2bool (env : string -> bool) (e : bexp) :=
  match e with
  | BETrue => true
  | BEFalse => false
  | BEConst b => b
  | BEVar x => env x
  | BENot e => negb (bexp2bool env e)
  | BEAnd e1 e2 => andb (bexp2bool env e1) (bexp2bool env e2)
  end.

(** true & (!x) *)
Example bexp_ex1 := BEAnd BETrue (BENot (BEVar "x")).

Section test.
  Variable benv : string -> bool.
  Compute bexp2bool benv bexp_ex1. 
  (* = if benv "x" then false else true
     : bool *)
End test.

(** AST到C字符串 *)
Fixpoint bexp2str (b2s : bool -> string) (e : bexp) : string :=
  match e with
  | BETrue => "true"
  | BEFalse => "false"
  | BEConst b => b2s b 
  | BEVar x => x
  | BENot e => "!(" ++ (bexp2str b2s e) ++ ")"
  | BEAnd e1 e2 => "(" ++ (bexp2str b2s e1) ++ " & " 
    ++ (bexp2str b2s e2) ++ ")"
  end.

Section test.
  Variable b2str : bool -> string.
  Compute bexp2str b2str  bexp_ex1. (* = "(true & !(x))" *)
End test.

(** 整数表达式AST *)
Inductive iexp :=
| IEConst (_ : Z)
| IEVar (_ : string)
| IEAdd (_ _ : iexp)
| IENeg (_ : iexp)
| IESub (_ _ : iexp)
.

(** AST到Coq类型 *)
Fixpoint iexp2Z (env : string -> Z) (e : iexp) :=
  match e with
  | IEConst i => i
  | IEVar x => env x
  | IEAdd e1 e2 => Z.add (iexp2Z env e1) (iexp2Z env e2)
  | IENeg e => Z.opp (iexp2Z env e)
  | IESub e1 e2 => Z.sub (iexp2Z env e1) (iexp2Z env e2)
  end.

(** 3 + (i1 - 4) *)
Example iexp_ex1 := IEAdd (IEConst 3) (IESub (IEVar "i1") (IEConst 4)).

Section test.
  Variable ienv : string -> Z.
  Compute iexp2Z ienv (IEConst 3).  (* = 3%Z *)
  Compute iexp2Z ienv (IEVar "i1"). (* = iexp_env "i1" *)
  
  Opaque Z.opp Z.sub.
  
  (* 注释，Compute 没有尊重 Opaque 声明 *)
  Compute iexp2Z ienv (IESub (IEConst 3) (IEConst 4)). (* = (-1)%Z *)
  (* 而 lazy 考虑了 *)
  Eval lazy in iexp2Z ienv (IESub (IEConst 3) (IEConst 4)). (* 
    = (3 - 4)%Z *)
  Eval lazy in iexp2Z ienv (IESub (IEVar "i1") (IEConst 4)). (* 
    = (iexp_env "i1" - 4)%Z *)
End test.

(** AST到C字符串 *)
Fixpoint iexp2str (i2s : Z -> string) (e : iexp) : string :=
  match e with
  | IEConst i => i2s i
  | IEVar x => x
  | IEAdd e1 e2 => "(" ++ (iexp2str i2s e1) ++ " + " ++ (iexp2str i2s e2) ++ ")"
  | IENeg e => "-(" ++ (iexp2str i2s e) ++ ")"
  | IESub e1 e2 => "(" ++ (iexp2str i2s e1) ++ " - " ++ (iexp2str i2s e2) ++ ")"
  end.

Section test.
  Variable i2s : Z -> string.

  Compute iexp2str i2s (IEConst 3). (* = i2s 3 *)
  Compute iexp2str i2s (IEVar "x"). (* = "x" *)
  Opaque i2s.
  Compute iexp2str i2s (IEAdd (IEConst 3) (IEConst 4)).
  Eval lazy in iexp2str i2s (IEAdd (IEConst 3) (IEConst 4)).
  Opaque append.  (* append 也需要设置为不透明，以便直观的看到结果 *)
  Eval lazy in iexp2str i2s (IEAdd (IEConst 3) (IEConst 4)). (*
    = "(" ++ i2s 3 ++ " + " ++ i2s 4 ++ ")" *)
End test.

(* C数据类型的AST *)
Inductive dataT :=
| Bool (v : bexp)
| Int32 (v : iexp)
| Float (v : R)
.

(* AST到Carrier的表达式 *)
Definition data2bexp (d : dataT) : option bexp :=
  match d with Bool v => Some v | _ => None end.
Definition data2iexp (d : dataT) : option iexp :=
  match d with Int32 v => Some v | _ => None end.
Definition data2rexp (d : dataT) : option R :=
  match d with Float v => Some v | _ => None end.

(* AST到Coq类型 *)
Definition data2bool (benv : string -> bool) (d : dataT) : option bool :=
  match (data2bexp d) with 
  | Some v => Some (bexp2bool benv v) 
  | _ => None 
  end.
Definition data2Z (ienv : string -> Z) (d : dataT) : option Z :=
  match (data2iexp d) with 
  | Some v => Some (iexp2Z ienv v) 
  | _ => None 
  end.
Definition data2R (d : dataT) : option R := data2rexp d.

(* AST到C字符串(仅类型)。例如 int *)
Definition data2strT (d : dataT) : string :=
  match d with
  | Bool _ => "bool"
  | Int32 _ => "int"
  | Float _ => "float"
  end.
(* AST到C字符串(仅值)。例如 (a + b) *)
Definition data2strV (b2s : bool -> string) (i2s : Z -> string) (d : dataT) 
  : string :=
  match d with
  | Bool v => bexp2str b2s v
  | Int32 v => iexp2str i2s v
  | Float _ => "??"
  end.

Example data_i3 := Int32 (IEConst 3).
Example data_i4 := Int32 (IEConst 4).
Example data_i5 := Int32 (IEAdd (IEConst 3) (IEConst 4)). (* 3 + 4 *)
Example data_b1 := Bool (BEAnd (BEAnd BETrue BEFalse) (BEVar "x")).

Section test.
  Variable b2s : bool -> string.
  Variable i2s : Z -> string.
  Eval lazy in data2strV b2s i2s data_b1.  (* = "((true & false) & x)" *)
  Opaque append.
  Eval lazy in data2strV b2s i2s data_i5.  (* 
    = "(" ++ i2s 3 ++ " + " ++ i2s 4 ++ ")" *)
End test.


(** tag-ed data *)
Definition tdataT : Type := string * dataT.

(* 计算tdataT的C字符串(类型 + 名称)。例如 int a *)
Definition tdata2str (x : tdataT) : string :=
  let '(t,d) := x in
    (data2strT d) ++ " " ++ t.

Example tdata_a_i3 : tdataT := ("a", data_i3).
Example tdata_b_i4 : tdataT := ("b", data_i4).
Compute tdata2str tdata_a_i3. (* = "int a" *)

(** C函数 - Signature *)
Module Type CFuncSig.
  
  Parameter name : string.
  Parameter iports : list tdataT.
  Parameter oport : dataT.
  
End CFuncSig.

(* 计算输入参数列表的C字符串。例如 int a, bool b *)
Definition iports2str (l : list tdataT) : string :=
  concat ", " (map (fun t => tdata2str t) l).
  
(** C代码生成。最简陋的版本，只处理函数 *)
Module CGen (F : CFuncSig).
  
  Parameter b2s : bool -> string.
  Parameter i2s : Z -> string.
  
  (** 生成函数的C字符串。例如 int xxx (int a, int b) { return a + b; } *)
  Definition funstr : string :=
    let s_retT := data2strT F.oport in
    let s_iports := iports2str F.iports in
    let s_body := data2strV b2s i2s F.oport in
      s_retT ++ " " ++ F.name ++ " (" ++ s_iports ++ ") { " 
        ++ "return " ++ s_body ++ "; }".
  
End CGen.


(** int (int a, int b) { return a + b + b; } *)
Module CGen_intfun1 <: CFuncSig.
  
  Parameter ia ib : Z.
  Parameter s2i : string -> Z. 
  
  (* 使用常量 *)
  Definition a1 : dataT := Int32 (IEConst ia).
  Definition b1 : dataT := Int32 (IEConst ib).
  
  (* 使用字符串变量 *)
  Definition a : dataT := Int32 (IEVar "a").
  Definition b : dataT := Int32 (IEVar "b").
  
  Definition name := "intfun1".
  Definition iports := [("a",a); ("b",b)].
  
  (* 定义计算过程 *)
  Definition oport1 : dataT :=
    match (data2iexp a1), (data2iexp b1) with
    | Some e1, Some e2 => Int32 (IEAdd (IEAdd e1 e2) e2)
    | _, _ => Int32 (IEConst 0)
    end.
  
  Definition oport : dataT :=
    match (data2iexp a), (data2iexp b) with
    | Some e1, Some e2 => Int32 (IEAdd (IEAdd e1 e2) e2)
    | _, _ => Int32 (IEConst 0)
    end.
  
  (** 形式规范 *)
  Definition spec1 : Prop := match (data2Z s2i oport1) with
    | Some z => z = (ia + ib + ib)%Z
    | _ => False
    end.
  
  Definition spec2 : Prop := match (data2Z s2i oport) with
    | Some z => z = (s2i "a" + s2i "b" + s2i "b")%Z
    | _ => False
    end.
  
  (** 形式验证 *)
  Lemma spec1_ok : spec1.
  Proof.
    unfold spec1. simpl. auto.
  Qed.

  Lemma spec2_ok : spec2.
  Proof.
    unfold spec2. simpl. auto.
  Qed.
  
End CGen_intfun1.

(** 代码生成 *)
Module cgen_intfun1 := CGen CGen_intfun1.
Compute cgen_intfun1.funstr.

(** 抽取到OCaml代码 *)

Require Import Extraction.

(* Extract *)
Recursive Extraction cgen_intfun1.


