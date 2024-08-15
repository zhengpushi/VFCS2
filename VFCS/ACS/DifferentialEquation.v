(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : 微分方程
  author      : Zhengpu Shi
  date        : 2022.08
  
  ref         :
  1. 《自动控制原理》 清华大学出版社 卢京潮
  
  remark      :
  1. 线性定常微分方程 (LTIDE: Linear, Time-Invariant Differential Equation)
    这是控制系统的数学模型（微分方程）的一个重要分类，传统上通过观察方程的形式来判别，
    我们试图用程序来自动判别。
    方法：将方程结构建立为AST，通过分析数据而判别方程结构；同时还要注意这种语法层面的
      操作是否和语义层面保持一致。
    
*)

Require Export Reals.
Require Export Lra.
Require Export FuncExt StrExt.

Open Scope string_scope.
Open Scope R_scope.


(* ######################################################################### *)
(** * 微分方程 *)

(* ======================================================================= *)
(** ** Syntax *)

(** 函数表达式 AST *)
(* 关于减法和取反，有两种逻辑：
  按照群论的思维，a - b 被定义为 a + (-b)
  按照另一种思路， - a 可以被定义为 0 - a
  同理，除法也有类似的问题。
*)
Inductive Fexp :=
| Fcnst (v : R -> R)
| Fvar (x : string)
| Fadd (e1 e2 : Fexp)
| Fsub (e1 e2 : Fexp)
| Fmul (e1 e2 : Fexp)
| Fdiv (e1 e2 : Fexp)
| Fcmul (a : R) (e : Fexp)
| Fderiv (e : Fexp)
.

(** 自动类型转换 *)
Coercion Fvar : string >-> Fexp.

(** 新的作用域 *)
Declare Scope F_scope.
Delimit Scope F_scope with F.
Open Scope F_scope.

(** 记号 *)
Infix "+" := Fadd : F_scope.
Infix "-" := Fsub : F_scope.
Infix "*" := Fmul : F_scope.
Infix "/" := Fdiv : F_scope.
Notation "a c* b" := (Fcmul a b) (at level 40, left associativity) : F_scope.
Notation "a '"   := (Fderiv a     ) (at level 20) : F_scope.

(** AST化简法则 *)
Axiom Fcmul_distr_l : forall a b f, a c* (b c* f) = (a * b) c* f.
Axiom Fderiv_cmul : forall a f, (a c* f)' = a c* f '.
(* Axiom Fderiv_c *)

(** RLC串联电路示例（自控ppt-96-03,page9），也是陈老师给出的微积分推导示例 *)
Section test.
  Variable R L C : R.
  Variable ur uc : string.
  
  Let i := C c* uc '.
  Hypothesis eq1 : Fvar ur = L c* i ' + R c* i + uc.
  
  Goal Fvar ur = (L * C) c* uc '' + (R * C) c* uc ' + uc.
  Proof.
    rewrite eq1. unfold i.
    rewrite Fderiv_cmul.
    rewrite ?Fcmul_distr_l. auto.
  Qed.
  
End test.

(* ======================================================================= *)
(** ** Semantics *)

(* --------------------------------------------------------------------- *)
(** *** 函数的算术运算 *)

(* 现在开始，主要使用 R 作用域 *)
Open Scope R_scope.

(** 函数类型：从实数到实数 *)
Definition tpRFun := R -> R.

(** 泛函类型：从实函数到实函数 *)
Definition tpRFunctional := (R->R) -> (R->R).

(* 定义函数算术运算：加法、减法、乘法、除法、常数乘法 *)
Definition fadd (f:R->R) (g:R->R) (t:R) : R := f t + g t.
Definition fsub (f:R->R) (g:R->R) (t:R) : R := f t - g t.
Definition fmul (f:R->R) (g:R->R) (t:R) : R := f t * g t.
Definition fdiv (f:R->R) (g:R->R) (t:R) : R := f t / g t.
Definition fcmul (c:R) (f:R->R) (t:R) : R := c * (f t).

(** 给二元函数定义中缀记号 *)
Infix "+f" := fadd (at level 50, left associativity) : R_scope.
Infix "-f" := fsub (at level 55, left associativity) : R_scope.
Infix "*f" := fmul (at level 43, left associativity) : R_scope.
Infix "/f" := fdiv (at level 46, left associativity) : R_scope.
Infix "c*" := fcmul (at level 40, left associativity) : R_scope.

(** 函数算术运算的合法性 *)

Lemma fadd_ok : forall (u v : R->R) (t:R), (u +f v) t = u t + v t.
Proof. auto. Qed.

Lemma fsub_ok : forall (u v : R->R) (t:R), (u -f v) t = u t - v t.
Proof. auto. Qed.

Lemma fmul_ok : forall (u v : R->R) (t:R), (u *f v) t = u t * v t.
Proof. auto. Qed.

Lemma fdiv_ok : forall (u v : R->R) (t:R), (u /f v) t = u t / v t.
Proof. auto. Qed.

Lemma fcmul_ok : forall (u : R->R) (c:R) (t:R), (c c* u) t = c * u t.
Proof. auto. Qed.

(** 函数算术运算的性质 *)

Lemma fadd_assoc : forall (u v w:R->R), (u +f v) +f w = u +f (v +f w).
Proof. intros. extensionality x. rewrite !fadd_ok. ring. Qed.

Lemma fadd_comm : forall (u v : R->R), (u +f v) = (v +f u).
Proof. intros. extensionality x. rewrite !fadd_ok. ring. Qed.

Lemma fmul_assoc : forall (u v w:R->R), (u *f v) *f w = u *f (v *f w).
Proof. intros. extensionality x. rewrite !fmul_ok. ring. Qed.

Lemma fmul_comm : forall (u v : R->R), (u *f v) = (v *f u).
Proof. intros. extensionality x. rewrite !fmul_ok. ring. Qed.

Lemma fcmul_assoc1 : forall (c d:R) (u:R->R), c c* (d c* u) = (c * d) c* u.
Proof. intros. extensionality x. rewrite !fcmul_ok. ring. Qed.

Lemma fcmul_assoc2 : forall (c:R) (u v : R->R), c c* (u *f v) = (c c* u) *f v.
Proof.
  intros. extensionality x. rewrite !fcmul_ok,!fmul_ok,!fcmul_ok. ring.
Qed.

Lemma fcmul_add_distr : forall (c:R) (u v:R->R),
  c c* (u +f v) = c c* u +f c c* v.
Proof.
  intros. extensionality x. repeat rewrite ?fcmul_ok,?fadd_ok. ring.
Qed.

(* --------------------------------------------------------------------- *)
(** *** 导函数及相关公理 *)

(** 导数算子 *)
Parameter deriv : (R->R) -> (R->R).
Notation "f '" := (deriv f) (at level 20) : R_scope.

(* COQ标准库中包含了关于导函数的一个库Rderiv。
按理，我们关于导函数问题的推理应该从这个库所建立的数学引理开始。
但是那些引理的结构比较复杂，在目前阶段，我们可以先直接引入一些熟知的
关于导函数的等式作为公理，在此基础上进行证明开发工作。*)

(* (u + v)' = u' + v' *)
Axiom deriv_add : forall (u v:R->R), (u +f v)' = u ' +f v '.
(* (u - v)' = u' - v' *)
Axiom deriv_sub : forall (u v:R->R), (u -f v)' = u ' -f v '.
(* (c * v)' = c * v' *)
Axiom deriv_cmul : forall (v:R->R) (c:R), (c c* v)' = c c* v '.
(* (u * v)' = u' * v + u * v' *)
Axiom deriv_mul : forall (u v:R->R), (u *f v)' = u ' *f v +f u *f v '.

(* ======================================================================= *)
(** ** 语法到语义的解释 *)

(** 将 AST 转为 R 上的表达式 *)
Section F2R.
  Variable env : string -> (R -> R).
  
  Fixpoint F2R (f : Fexp) : R -> R :=
    match f with
    | Fcnst f => f
    | Fvar x => env x
    | Fadd e1 e2 => F2R e1 +f F2R e2
    | Fsub e1 e2 => F2R e1 -f F2R e2
    | Fmul e1 e2 => F2R e1 *f F2R e2
    | Fdiv e1 e2 => F2R e1 /f F2R e2
    | Fcmul a e => a c* F2R e
    | Fderiv e => deriv (F2R e)
    end.
End F2R.

(** RLC串联电路示例（自控ppt-96-03,page9），也是陈老师给出的微积分推导示例 *)
Section test.
  Open Scope F.
  
  Variable R1 L C : R.
  Let ur := "ur".
  Let uc := "uc".
  
  Let i := C c* uc '.
  Let exp1 := Fvar ur.
  Let exp2 := L c* i ' + R1 c* i + uc.
  Let exp3 := (L * C) c* uc '' + (R1 * C) c* uc ' + uc.
  Hypothesis eq1 : exp1 = exp2.
  Hypothesis eq2 : exp1 = exp3.
  
  (* 定义环境 *)
  Variable r c NA : R -> R.
  Let env := fun (x : string) =>
    if (x =? ur) then r
    else if (x =? uc) then c
    else NA.
  
  Open Scope R.
  (* 测试转换效果 *)
(*   Compute F2R env exp1. *)
(*   Compute F2R env exp2. *)
(*   Compute F2R env exp3. *)
  (* 按名称调用，而不是按值调用，则会保留函数形式 *)
(*   Eval cbn in (F2R env exp2). *)
(*   Eval cbn in (F2R env exp3). *)
  
End test.



(* ######################################################################### *)
(** * 线性定常微分方程(LTIDE) *)


(* ======================================================================= *)
(** ** 证明LTIDE的一般形式满足叠加原理 *)

(** *** 从语义上证明 *)

(** n阶导数 *)
Definition nderiv (f:R->R) (n:nat) : R->R := nexec f deriv n.

(** 环境 *)
(* Compute repeat R 10. *)

(** 线性定常微分方程的一般形式的某一侧 *)

(** 使用列表来存储系数 *)
Definition create_exp (n:nat) (f:R->R) (coefs:list R) :=
  let g := (fun i => (nth i coefs 1) c* (nderiv f (S i))) in
  let l := map g (seq 0 n) in
    fold_left fadd l f.

(** 使用一个函数来表示系数 *)
Definition create_exp_f (n:nat) (f:R->R) (coefs:nat -> R) :=
  let g := (fun i => (coefs i) c* (nderiv f (S i))) in
  let l := map g (seq 0 n) in
    fold_left fadd l f.

(** 示例：在有限项上验证叠加原理 *)
Section test.
  (* 第一组 *)
  
  (* 输出函数、输入函数 *)
  Variable c1 r1 : R->R.
  (* 系数。这里是手动给定的有限个值，如何模拟无限多个实数变量在后文讨论 *)
  Variable a1 a2 a3 a4 a5 : R.
  Variable b1 b2 b3 b4 : R.
  Let coefs_c1 : list R := [a1;a2;a3;a4;a5].
  Let coefs_r1 : list R := [b1;b2;b3;b4].
  (* 得到了单侧的表达式 *)
  (* Eval cbn in create_exp 5 c1 coefs_c1. *)
  (* Eval cbn in create_exp 3 r1 coefs_r1. *)
  (* 构造微分方程 *)
  Hypothesis eq1 : create_exp 5 c1 coefs_c1 = create_exp 4 r1 coefs_r1.

  (* 第二组 *)
  Variable c2 r2 : R->R.
  Variable e1 e2 e3 e4 : R.
  Variable f1 f2 f3 : R.
  Let coefs_c2 : list R := [e1;e2;e3;e4].
  Let coefs_r2 : list R := [f1;f2;f3].
  (* Eval cbn in create_exp 4 c2 coefs_c2. *)
  (* Eval cbn in create_exp 3 r2 coefs_r2. *)
(*   Let eq2L :=  *)
  Hypothesis eq2 : create_exp 4 c2 coefs_c2 = create_exp 3 r2 coefs_r2.
  
  (** 验证叠加原理 *)
  Variable A B : R.   (* 线性叠加系数 *)
  Goal create_exp 5 (A c* c1) coefs_c1 +f create_exp 4 (B c* c2) coefs_c2 =
       create_exp 4 (A c* r1) coefs_r1 +f create_exp 3 (B c* r2) coefs_r2.
  Proof.
    cbn in *. repeat rewrite ?deriv_cmul in *.
    rewrite ?fcmul_assoc1.
    repeat match goal with
    | |- context [?a * A] => replace (a * A) with (A * a); try ring
    | |- context [?a * B] => replace (a * B) with (B * a); try ring
    end.
    rewrite <- ?fcmul_assoc1.
    rewrite <- ?fcmul_add_distr. rewrite eq1,eq2. auto.
  Qed.
  
End test.

(** 示例：在无限项上验证叠加原理 *)

(* 用于化简"导数、求和"的引理 *)
Lemma sum_deriv_rw : forall (a:nat->R) (f:R->R) (A:R) (n:nat),
  fold_left fadd (map (fun i:nat => a i c* nexec ((A c* f) ') deriv i) 
  (seq 0 n)) (A c* f)
  = A c* (fold_left fadd (map (fun i:nat => a i c* nexec (f ') deriv i)
    (seq 0 n)) f).
Proof.
  intros a f A n.
  remember (fun i : nat => a i c* nexec ((A c* f) ') deriv i) as F.
  remember (fun i : nat => a i c* nexec (f ') deriv i) as G.
(*   clear. *)
  induction n.
  - cbv. auto.
  - rewrite ?fold_map_seq. rewrite IHn. rewrite fcmul_add_distr. f_equal.
    rewrite HeqF,HeqG. extensionality x.
    rewrite fcmul_assoc1. rewrite Rmult_comm. rewrite <- fcmul_assoc1. f_equal.
    (* 目标： (A * f)' 的 n 阶导数 = A * (f ' 的 n 阶导数 *)
    (* goal: (nexec ((A c* f) ') deriv n) = (A c* (nexec (f ') deriv n)) *)
    clear.
    rewrite ?nexec_rw. rewrite <- deriv_cmul. f_equal.
    rewrite nexec_linear. auto. intros. apply deriv_cmul.
Qed.

Section test.
  (* 第一组 *)
  
  (* 输出函数、输入函数 *)
  Variable c1 r1 : R->R.
  (* 系数。模拟无限多个实数变量 *)
  Variable a1 : nat -> R.
  Variable b1 : nat -> R.
  (* 得到了单侧的表达式 *)
  (* Eval cbn in (create_exp_f 5 r1 a1). *)
  (* Eval cbn in (fun n => create_exp_f n r1 a1) 5%nat. *)
  (* 构造微分方程 *)
  Hypothesis eq1 : forall n1 m1, create_exp_f n1 c1 a1 = create_exp_f m1 r1 b1.

  (* 第二组 *)
  Variable c2 r2 : R->R.
  Variable a2 : nat -> R.
  Variable b2 : nat -> R.
  Hypothesis eq2 : forall n2 m2, create_exp_f n2 c2 a2 = create_exp_f m2 r2 b2.
  
  (** 验证叠加原理 *)
  Variable A B : R.   (* 线性叠加系数 *)
  Goal forall n1 m1 n2 m2,
    create_exp_f n1 (A c* c1) a1 +f create_exp_f n2 (B c* c2) a2 =
    create_exp_f m1 (A c* r1) b1 +f create_exp_f m2 (B c* r2) b2.
  Proof.
    intros. unfold create_exp_f in *. cbn in *.
    rewrite ?sum_deriv_rw.
    rewrite (eq1 n1 m1). rewrite (eq2 n2 m2). auto.
  Qed.

End test.





(* ======================================================================= *)
(** ** 判别一个方程是否为 LTIDE *)

(** 一些思路
1. 分左右两侧两个表达式来判别
2. 左侧是输出有关，右侧是输入有关
3. 单侧，以输出为例，只能是输出项、输出项的各阶导数项，不能含有交叉乘积、常数
  a. 这里的常数，实际是常函数。
  b. 所谓的一项，是乘、除、求导、数乘构成的项
  c. 各个项之间用加法或减法连接
  d. 一个表达式可能化简不完全，比如 (f1 + f2) * f3 应当展开称 f1 * f3 + f2 * f3
4. 举例
  (1).  c'' + 2 * c' * c + 5 = 2 * c' * r
    含有交叉乘积项 2 * c' * c 和 2*c'*r，含有常数项 5，所以不是线性的。
    再看系数，都是常数，所以是定常的。
  (2). c' + cos * c = 2 * r
    线性，非定常。
 
*)
