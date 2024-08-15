(*
  Copyright 2023 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Differential calculus by Coquelicot
  author    : Zhengpu Shi
  date      : 2023.03
  
  remark    :
  1. Currently, most properties are axiomatically implemented, since the
     main work on calculus is being done by another group in our team.
     目前，大多数性质都是公理化实现，因为微积分的主要工作是我们团队的另一个组在做。

  reference :
  1. Coquelicot library
  2. 高等数学学习手册，徐小湛

 *)

(* From Coquelicot Require Export Rbar Continuity Derive RInt AutoDerive. *)

Require List.
From Coquelicot Require Coquelicot.

Module problem_of_notation_in_Coquelicot.
  (* 当我按如下方式导入这两个库，先导入 ListNotations，再导入 Coquelicot *)
  Import List. Import ListNotations.
  Import Coquelicot.

  (* 则，[1] 会被解释为 nat * unit 类型 *)
  (* Check [1]. (* : nat * unit *) *)

  (* 即使再次导入 ListNotations 库，仍然无法改变这个记号的行为 *)
  Import ListNotations.
  (* Check [1]. (* : nat * unit *) *)

  (* 最后无奈，使用 Disable Notation 可以解决。
     但是，这又带来了多余的提示信息，该消息无法屏蔽，而且会在所有间接使用该库的地方显示，
     这打乱了编译时的输出提示。*)

  (* Disable Notation "[ x1 , .. , xn ]". *)

  (* 更多讨论，请参考 https://coq.discourse.group/t/suppressing-repeated-warnings-from-disable-notation-command-in-coq/2339 for more discussion. *)

  (* 一个投机的办法是，在ListNotations导入之前先导入 Coquelicot 库 *)
End problem_of_notation_in_Coquelicot.

From Coquelicot Require Export Coquelicot.
Export List. Export ListNotations.

From FinMatrix Require Export RFunExt.


(* We won't expose the the details of the differential technique *)
#[global] Opaque Derive.
#[global] Opaque ex_derive.


(* ######################################################################### *)
(** * Additional properties for real functions *)

(* ======================================================================= *)
(** ** Normalization of functions (i.e., change the form of a function) *)

Lemma norm_fsub : forall f g : R -> R, (fun x => (f x + - g x)) = (fun x => (f x - g x)).
Proof. auto. Qed.

Lemma norm_fdiv : forall f g : R -> R, (fun x => (f x * / g x)) = (fun x => (f x / g x)).
Proof. auto. Qed.


(* ######################################################################### *)
(** * derivable 可导的 *)

(* ======================================================================= *)
(** ** Definitions of derivable  *)

(** derivable function *)
Definition derivable (u : R -> R) : Prop := forall x, ex_derive u x.

Lemma derivable_id : derivable (fun x : R => x).
Proof. hnf; intros. apply ex_derive_id. Qed.

Lemma derivable_add : forall u v, derivable u -> derivable v -> derivable (u +f v).
Proof.
  intros. unfold derivable in *; intros. autounfold with RFun.
  pose proof (ex_derive_plus u v) as Hd; apply Hd; auto.
Qed.

Lemma derivable_opp : forall u, derivable u -> derivable (-f u).
Proof.
  intros. unfold derivable in *; intros. autounfold with RFun.
  pose proof (ex_derive_opp u) as Hd; apply Hd; auto.
Qed.

Lemma derivable_cmul : forall c u, derivable u -> derivable (c s* u).
Proof.
  intros. unfold derivable in *; intros. autounfold with RFun.
  pose proof (ex_derive_scal u) as Hd; apply Hd; auto.
Qed.

Lemma derivable_mul : forall u v, derivable u -> derivable v -> derivable (u *f v).
Proof.
  intros. unfold derivable in *; intros. autounfold with RFun.
  pose proof (ex_derive_mult u v) as Hd; apply Hd; auto.
Qed.

#[export] Hint Resolve
  derivable_id
  derivable_add
  derivable_opp
  derivable_cmul
  derivable_mul
  : deriv.


(* ######################################################################### *)
(** * Derivative functions 导函数 *)

(* ======================================================================= *)
(** ** Definitions of derivative operation 导函数  *)

Section test.
  (* 导函数的定义 *)
  Import Coquelicot.Coquelicot.
  Variable f : R -> R.
  (* Check Derive f.    (* : R -> R *) *)
End test.
  

(** derivative operator *)
Notation "f '" :=
  (Derive f) (at level 10, left associativity, format "f '") : RFun_scope.

(* 1st-order derivative *)
(* Notation "f '" := *)
(*   (Derive f) (at level 10, left associativity, format "f '") : Rfun_scope. *)

(* Now, 2nd-order or 3st-order derivative could be: f '', f ''' *)


(** Derivative models can describe many phenomena in natural science and social science
    导数模型可以刻画很多自然科学和社会科学中的现象
 *)
Section practice_models_using_derivative.

  (* 2D曲线 => 切线斜率 *)
  Let k (f : R -> R) x := f ' x.
  (* 2D曲线 => 法线斜率 *)
  Let k' (f : R -> R) x := (- (1 / f ' x)).
  (* 路程 => 速度 *)
  Let v (s : R -> R) : R -> R := fun t => s ' t.
  (* 路程 => 加速度 *)
  Let a (v : R -> R) : R -> R := fun t => v '' t.
  (* 旋转角度 => 角速度 *)
  Let ω (θ : R -> R) t := θ ' t.
  (* 电量 => 电流强度 *)
  Let I (Q : R -> R) t := Q ' t.
  (* 人口数量 => 人口增长率 *)
  Let v1 (P : R -> R) : R -> R := fun t => P ' t.

End practice_models_using_derivative.


(* ======================================================================= *)
(** ** Basic rules for derivatives *)

Lemma deriv_const : forall c, (fun x => c) ' = fun _ => 0.
Proof. feq. rewrite Derive_const; auto. Qed.

Fact deriv_id : (fun x => x) ' = fun _ => 1.
Proof. feq. apply Derive_id. Qed.

Lemma deriv_id' : id ' = fun _ => 1.
Proof. feq. rewrite Derive_id; auto. Qed.

Lemma deriv_add : forall u v, derivable u -> derivable v -> (u +f v)' = u ' +f v '.
Proof. feq. apply Derive_plus; auto. Qed.

Lemma deriv_opp : forall v, (-f v) ' = -f (v ').
Proof. feq. rewrite Derive_opp; auto. Qed.

Lemma deriv_sub : forall u v, derivable u -> derivable v -> (u -f v)' = u ' -f v '.
Proof. feq. apply Derive_minus; auto. Qed.

Lemma deriv_cmul : forall c u, (c s* u)' = c s* u '.
Proof. feq. apply Derive_scal. Qed.

Lemma deriv_mul : forall u v, derivable u -> derivable v -> (u *f v)' = u ' *f v +f u *f v '.
Proof. feq. apply Derive_mult; auto. Qed.

(* 这里的 (forall t, v t <> 0) 太强了，只需要在求导的点处非零即可 *)
Lemma deriv_inv : forall (v : R -> R),
    (forall t, v t <> 0) -> derivable v ->
    (/f v) ' = -f ((v ') / (v *f v)).
Proof. feq. rewrite Derive_inv; auto. ra. Qed.

Lemma deriv_div : forall u v,
    (forall t, v t <> 0) -> derivable u -> derivable v ->
    (u /f v)' = (u ' *f v -f u *f v ') /f (v *f v).
Proof. feq. rewrite norm_fdiv. rewrite Derive_div; auto. ra. Qed.

#[export] Hint Rewrite
  deriv_const deriv_id deriv_id'
  deriv_add deriv_opp
  deriv_sub
  deriv_cmul
  deriv_mul
  deriv_inv
  deriv_div
  : deriv.

(** Automation for derivative *)
Ltac deriv :=
  intros; autorewrite with deriv; auto with deriv;
  try feq.

Section test.

  Goal (fun x => x)' = fone.
  Proof. deriv. Qed.

  Goal forall f g h, derivable f -> derivable g -> derivable h ->
                (f +f g -f h)' = f ' +f g ' -f h '.
  Proof. deriv. Qed.
End test.


(** ** 基本初等函数的导数公式 *)

Lemma deriv_Ropp : (Ropp)' = -f fone.
Proof. replace Ropp with (-f id); auto. deriv. Qed.

Lemma deriv_Rinv : (Rinv) ' = fun x => -(/(x*x)).
Proof.
  replace Rinv with (/f (fun x => x)); auto. deriv.
  unfold div_fct. ra.
Admitted.

Lemma deriv_fpower : forall a, (Rpower a)' = a s* (Rpower (a-1)).
Proof. intros. Admitted.

Fact deriv_sqrt : (sqrt) ' = (fun x => 1 / (2 * sqrt x))%R.
  (* Proof. *)
  (*   rewrite <- fpower_1_2_eq. rewrite deriv_fpower. *)
  (*   feq; intros. cbv. *)
  (*   rewrite ?Rmult_assoc. f_equal. *)
  (*   rewrite Rpower_plus. *)
  (*   rewrite Rpower_Ropp. ring_simplify. *)
  (*   replace (R1 * / (R1 + R1))%R with (/2)%R; try lra. *)
  (*   rewrite Rpower_sqrt. rewrite Rpower_1. *)
  (*   assert (t = Rsqr (sqrt t)). *)
  (*   { rewrite Rsqr_sqrt; auto. admit. } *)
  (*   rewrite H at 2. cbv. field. *)
  (* Admitted. (* ToDo: need more hypothesis *) *)
Abort.

Fact deriv_sin : sin ' = cos. Admitted.
Fact deriv_cos : cos ' = sin. Admitted.
Fact deriv_tan : tan ' = sec *f sec. Admitted.
Fact deriv_cot : cot ' = -f (csc *f csc). Admitted.
(* Fact deriv_sec : sec ' = (sec *f tan). Admitted. *)
(* Fact deriv_csc : csc ' = - (csc *f cot). Admitted. *)

(* Fact deriv_exp : exp ' = exp. Admitted. *)
(* Fact deriv_flog : forall a, (flog a) ' = / ((ln a) \.* fid). Admitted. *)
(* Fact deriv_fln : ln ' = finv fid. Admitted. *)
(* Fact deriv_asin : asin ' = (fun x => / (sqrt (1 - x * x)))%R. Admitted. *)
(* Fact deriv_acos : acos ' = (fun x => - / (sqrt (1 - x * x)))%R. Admitted. *)
(* Fact deriv_atan : atan ' = (fun x => / (1 + x * x))%R. Admitted. *)
(* Fact deriv_acot : acot ' = (fun x => - / (1 + x * x))%R. Admitted. *)
(* Fact deriv_asec : asec ' = (fun x => / (x * (sqrt (x * x - 1))))%R. Admitted. *)
(* Fact deriv_acsc : acsc ' = (fun x => - / (x * (sqrt (x * x - 1))))%R. Admitted. *)

(** 导数的线性性质 *)
Fact deriv_linear : forall c1 c2 u1 u2,
    derivable u1 -> derivable u2 ->
    (c1 s* u1 +f c2 s* u2)' = c1 s* u1 ' +f c2 s* u2 '.
Proof. deriv. Qed.

(** 乘法求导推广 *)
Fact deriv_mul3 : forall u v w,
    derivable u -> derivable v -> derivable w -> 
    (u *f v *f w)' = u ' *f v *f w +f u *f v ' *f w +f u *f v *f w '.
Proof. deriv. Qed.


(** 复合函数的求导法则：链式法则 *)
Lemma deriv_comp : forall u v,
    (forall t, ex_derive u (v t)) -> derivable v ->
    (fun x => u (v x))' = (fun x => (u ' (v x)) * (v ' x))%R.
Proof. deriv. rewrite Derive_comp; auto. ra. Qed.

(* Section ex_2_2_3_page73. *)
(*   Goal (fun x => fexp 2 (Rsqr (sin (/x))))' = *)
(*          (fun x => (- (ln 2) / (x*x)) * (fexp 2 (Rsqr (sin (/x)))) * sin (2/x))%R. *)
(*   Proof. *)
(*     remember (fun u => fexp 2 u) as y. *)
(*     remember (Rsqr) as u. *)
(*     remember (sin) as v. *)
(*     remember (fun x => /x)%R as w. *)
(*     rewrite (fcomp_rw y), (fcomp_rw u), (fcomp_rw v). *)
(*     rewrite ?deriv_comp. *)
(*     rewrite Heqy, Hequ, Heqv, Heqw. clear. *)
(*     feq; intros. *)
(*     rewrite deriv_fexp. *)
(*     rewrite <- fpower_2_eq''. rewrite deriv_fpower. *)
(*     rewrite deriv_sin. *)
(*     rewrite deriv_inv'. *)
(*     (* all the derivivate have been eliminated *) *)
(*     cbv. *)
(*     (* now, all the functions were eliminated, only remain expressions of R type *) *)
(*     ring_simplify. *)
(*   (* 因为有 ln, Rpower, sin, 等，所以 lra 无法解决， *)
(*          但又不能总是手工消除，因为数学工作量本来就大，再加上形式化时引入的各种机制 *)
(*          使问题变得更为复杂，故而手工消除不可取。 *)
(*          因此，如果能有一种聪明的tactic，可以消除这类等式或不等式问题，将极大的提高 *)
(*          实数问题的证明速度。*) *)
(*   Abort. *)

(* End ex_2_2_3_page73. *)
    
Section example_LCR_Problem.

  Variable L C R1 : R.
  Variables i uc ur : R -> R.

  (* 克希霍夫定律 *)
  Axiom kxmf1 : L s* i ' +f uc +f (R1 s* i) = ur.
  Axiom kxmf2 : i = C s* uc '.

  (** 待证命题（消去 i，对等式变形即可）  *)
  Let main_thm : Prop := (L * C) s* uc ' ' +f (R1 * C) s* uc ' +f uc = ur.

  Goal main_thm.
  Proof.
    hnf. rewrite <- kxmf1. rewrite kxmf2.
    rewrite deriv_cmul. feq.
  Qed.

(* 小结：函数等式的证明可以采用两种方法。
   一种是使用一组函数等式引理重写函数表达式来证明。
   另一种是直接把函数等式转变成实数等式来证明。
 *)

End example_LCR_Problem.


(** ** Known equations of derivative *)
Section deriv_equations.
  
  Theorem fconst_simp : forall x y, (fcnst x) y = x.
  Proof. auto. Qed.

  Theorem fid_simp : forall x, id x = x.
  Proof. intros. auto. Qed.

  Theorem deriv_fconst: forall C, (fcnst C)' = fzero.
  Proof. deriv. deriv. Qed.

  Theorem deriv_fone : (fone)' = fzero.
  Proof. unfold fone. apply deriv_fconst. Qed.

  Theorem deriv_fzero : (fzero)' = fzero.
  Proof. unfold fzero. apply deriv_fconst. Qed.

  (** (1/v)' = -v'/(v^2) *)
  Theorem deriv_inv'' : forall (v : R -> R),
      derivable v ->
      (* Here, different with "v <> fzero" *)
      (forall x, v x <> 0) ->
      (fone /f v)' = (-1) s* (v ') /f (v * v).
  Proof.
    intros.
    (* feq. *)
    unfold fone.
    repeat (
        try rewrite ?deriv_div;
        try rewrite ?deriv_fconst;
        try rewrite ?fdiv_ok;
        try rewrite ?fmul_ok;
        try rewrite ?fcmul_ok;
        try rewrite ?fadd_ok;
        try rewrite ?fsub_ok;
        try rewrite ?fid_simp;
        try rewrite fconst_simp); auto.
  (*   - autorewrite with R. field. *)
  (*     intro. specialize (H0 t). destruct H0. *)
  (*     ra. (* Tips: a good examples to show that "ra" is better than "lra" *) *)
  (*   - intro. auto. unfold fconst. unfold derivable. apply ex_derive_const. *)
    (* Qed. *)
  Abort.

End deriv_equations.
