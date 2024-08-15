(*
  purpose   : 临时头脑风暴，尝试建立{适合于飞控的，C的AST + 验证}
  author    : Zhengpu Shi
  date      : May 10, 2023

  特性：
  1. 数据类型：数组、结构体、整数、浮点数
  2. 表达式：赋值、顺序、条件、循环
  3. 扩展：函数调用

  动机：如何表示以下C程序的AST？
  struct s = {
    int i;
    struct s1 = {
      int j;
      int[3] a;
    }
  }

  int g_i = 3;
  float g_f = 2.0;
  struct g_s;

  void fun1 (int p1) {
    return p1 + 1;
  }
 
  int main(int argc, char** argv) {
    int i = 1;
    g_s.i = 1;
    g_s.s1.a[0] = 2;
    g_s.s1.a[5] = 3;  (* buggy code, we won't generate it. *)
    return 1;
  }
 *)

Require Import Matrix.
Require Import List. Import ListNotations.
Require Import Strings.String.
Require Import ZArith.
Require Import Reals.

Open Scope string.

(* 定长数组(向量)的实现 *)
Section vec.
  Variable A : Type.

  (* 向量表示为携带了一个函数的依赖类型 *)
  Inductive vec (n : nat) := mk_vec (f : nat -> A).

  (* 函数和向量之间的转换 *)
  Definition f2v (n : nat) (f : nat -> A) : vec n :=
    mk_vec n f.
  Definition v2f {n : nat} (v : vec n) : nat -> A :=
    let '(mk_vec _ f) := v in f.

  (* 列表和向量之间的转换 *)
  Definition l2v (n : nat) (A0 : A) (l : list A) : vec n :=
    f2v n (fun i => nth i l A0).
  Definition v2l (n : nat) (v : vec n) : list A :=
    map (fun i => v2f v i) (seq 0 n).
End vec.


(* 数据类型 *)
Inductive DataType :=
| DTbool
| DTint
| DTfloat
| DTvec (t : DataType) (n : nat)
| DTstruct (flds : list (string * DataType))
.

Section test.
  Compute DTbool. (* bool *)
  Compute DTint.  (* int *)
  Compute DTfloat. (* float *)
  Compute DTvec DTbool 3. (* bool[3] *)
  Compute DTvec (DTvec DTint 3) 2. (* (int[3])[2] *)
  Compute DTstruct [("b",DTbool); ("i",DTint)]. (* struct{ bool b; int i} *)
  Compute DTstruct [("i",DTint); ("v",DTvec DTbool 3)]. (* struct {int i; bool[3] v *)
  Compute DTstruct [
      ("i",DTint);
      ("s", DTstruct [("i", DTfloat);("v",DTvec DTint 3);("b",DTbool)]
    )].
(*
    struct ?? {
      int i;      (* a same field name in it's child *)
      struct s {
        float i;  (* a same field name in it's parent *)
        int[3] v;
        bool b;
      }
    }
 *)
End test.

(* 数据 *)
Inductive DataValue :=
| DVbool (b : bool)
| DVint (i : Z)
| DVfloat (f : R)
| DVvec (n : nat) (v : @vec DataValue n)
| DVstruct (s : list DataValue)
.

(* 默认值 *)
Fixpoint DataValueDef (t : DataType) : DataValue :=
  match t with
  | DTbool => DVbool false
  | DTint => DVint 0
  | DTfloat => DVfloat R0
  | DTvec t n => DVvec n (f2v _ n (fun i => DataValueDef t))
  | DTstruct f => DVstruct (map (fun '(s,t) => DataValueDef t) f)
  end.

Section test.

  (* 默认数据 *)
  Compute DataValueDef DTbool.
  Compute DataValueDef DTint.
  Compute DataValueDef (DTvec DTint 3). (* [0;0;0] : int[3] *)
  Compute DataValueDef (DTvec (DTvec DTint 3) 2). (* [[0;0;0];[0;0;0]] : (int[3])[2] *)
  Compute DataValueDef (DTstruct [("b",DTbool); ("i",DTint)]).
  (* {false; 0} : struct { bool b; int i } *)
  
  (* 构造自定义的数据 *)
  Compute DVbool true.
  Compute DVint 5.
  Compute DVfloat R1.
  (* 这里，使用了相同的数据类型 Dvint *)
  Compute DVvec 3 (l2v _ 3 (DataValueDef DTint) [DVint 1; DVint 2; DVint 3]).
  (* 但是，还是可以构造出不同类型上的数组，这不符合数组的语义。例如 *)
  Compute DVvec 3 (f2v _ _ (fun i =>
                              match i with
                              | 0 => DVint 3
                              | _ => DVfloat 2
                              end)).
  
  Compute DVstruct [DVint 3;DVfloat R1].
End test.

(* 基于AST的基本实矩阵理论 *)
Module RMAT.

  (* AST上的mat，简称 M *)
  Open Scope R.
  
  (* 使用嵌套列表创建矩阵 *)
  Definition l2M (r c : nat) (dl : list (list R)) :=
    f2v DataValue r
    (fun i => DVvec c
              (f2v DataValue c
                 (fun j => DVfloat (nth j (nth i dl []) R0)))).

  (* 将 mat 转换为 M *)
  Definition m2M (r c : nat) (m : @mat R r c) :=
    f2v DataValue r
    (fun i => DVvec c
              (f2v DataValue c
                 (fun j => DVfloat (m$i$j)))).


  (* 将任意 DataValue 转换为矩阵，只有 vec (vec R) 才认可 *)
  Check fun (d : DataValue) =>
          match d with
          | DVvec r v =>
              let '(mk_vec _ _ f) := v in
              (* match  with *)
              (* | DVvec c v' => Some c *)
              (* |_ => Some 0 *)
          (* end *)
              Some r
          | _ => None
          end.
  Definition M2m (d : DataValue) (r c : nat) : option (@mat R r c).
    destruct d.
    (* 4:{ inversion v. *)
    (* :  *)
    Abort.

  (* 矩阵加法 *)
  
  (** 3x3 矩阵 *)
  
End RMAT.  

(* 路径，左右值都可能用到 *)
(* Inductive Path := *)
(* | Pvar (x : string) *)
(* | Parr (v : DataValue) ( *)
(* (* 数组访问 *) *)
(* Inductive Array *)

(* 布尔语句 *)
Inductive Bexp :=
| BEtrue | BEfalse | BEvar (x : string)
| BEand (b1 b2 : Bexp) | BEor (b1 b2 : Bexp)
.

Section test.
  Compute BEtrue.
  Compute BEvar "a".
  Compute BEand BEtrue (BEvar "a").
End test.

(* 整数的算术语句 *)
Inductive Zexp :=
| ZEval (z : Z) | ZEvar (x : string)
| ZEadd (e1 e2 : Zexp) | ZEopp (e : Zexp) | ZEsub (e1 e2 : Zexp)
| ZEmul (e1 e2 : Zexp) | ZEinv (e : Zexp) | ZEdiv (e1 e2 : Zexp)
.

Section test.
  Compute ZEval 3.
  Compute ZEvar "i".
  Compute ZEadd (ZEval 3) (ZEvar "i").
End test.

(* 表达式 *)
Inductive Exp :=
| EB (e : Bexp)
| EZ (e : Zexp)
.

(* 命令 *)
Inductive Cmd :=
| Casign (name : string) (t : DataType) (v : DataValue)
| Cskip
| Cseq (c1 c2 : Cmd)
| Cif (c c1 c2 : Cmd)
| Cwhile (c b : Cmd)
.

Section test.

  (* 如何表示以下C程序的AST？
  struct s = {
    int i;
    struct s1 = {
      int j;
      int[3] a;
    }
  }

  int g_i = 3;
  float g_f = 2.0;
  struct s g_s;

  void fun1 (int p1) {
    return p1 + 1;
  }
 
  int main(int argc, char** argv) {
    int i = 1;
    g_s.i = 1;
    g_s.s1.a[0] = 2;
    g_s.s1.a[5] = 3;  (* buggy code, we won't generate it. *)
    return 1;
  }
   *)

  (* 构造 struct s 的类型 *)
  Let dts : DataType :=
        DTstruct
          [("i",DTint);
           ("s1", DTstruct [("j",DTint);("a",DTvec DTint 3)])].

  (* 构造赋值表示 *)
  Compute Casign "g_i" DTint (DVint 3).
  Compute Casign "g_f" DTfloat (DVfloat 2.0).
  Compute Casign "g_s" dts (DataValueDef dts).

  (* 构造函数？构造数组访问？*)

End test.

                                   


