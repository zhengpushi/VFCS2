(*
  purpose   : 形式化“电路分析基础 - 3.17 二阶电路的零输入响应”
  author    : Zhengpu Shi
  date      : 2024.08.13

  reference :
  1. 电路分析基础，西安电子科技大学，第三章动态电路
     https://www.bilibili.com/video/BV1J741157zD?p=62

  remark    :
  1. 以RLC串联电路为例，分析电容电压 uC(t) 的响应。
     首先以电压源 uS 作为激励来推导出微分方程：
        uC'' + (R/L) uC' + (/(LC)) uC = (/(LC)) uS    (1)

     然后令 uS 为零，得到零输入响应的微分方程：
        uC'' + (R/L) uC' + (/(LC)) uC = 0             (2)

     记 2α = R/L，ω0 = 1/sqrt(L*C)。称 α 为衰减指数，ω0 为谐振角频率，公式 (2) 可表示为
        uC'' + 2α uC' + ω0² uC = 0                    (3)
     
     该微分方程的特征方程为：p² + 2αp + ω0² = 0，其特征根为：
        p1,2 = -α ± √(α² - ω0²) = -(R/(2L)) ± sqrt ((R/(2L))² - 1/(LC))     (4)
     
     特征根有四种不同情况，零输入响应也有四种不同情况。
     设电路的初始状态 uC(0+) = U0，iL(0+)=0
     (1) α > ω0，过阻尼情况，
         p1,p2 是不相等的负实根，
         电容释放的能量一部分贮存于电感，一部分被电阻消耗；最终，初始贮能全部被电阻消耗
     (2) α = ω0，临界阻尼情况，
         p1,p2 是相等的负实根，
         与过阻尼类似
     (3) 0 < α < ω0，欠阻尼情况，
         p1,p2 是一对共轭复根，
         电容释放的能量大部分贮存于电感，一部分被电阻消耗，形成能量交换，出现振荡。
     (4) α = 0，无阻尼情形
         理想情况下，电阻 R = 0，无能量消耗，形成等幅的正弦振荡。
  2. ra 策略提高了自动化程度。
  3. feq 比 extensionality 要化简的更多，会展开函数作用
*)

(** * 二阶常系数齐次线性微分方程的求解 *)

(* 来自FinMatrix，包含 move2h, commutative 等引理或策略 *)
From FinMatrix Require Import RExt.
(* 来自VFCS，二阶常系数齐次线性微分方程的求解 *)
From VFCS Require Import HomoLDE2.

(** 在VFCS库中，补充了函数算术运算、求导运算的记号 *)

(* 函数的数乘运算 *)
Locate "s*".
(* Notation "x s* y" := (fscal x y) : RFun_scope (default interpretation) *)

(* 求导记号 *)
Locate " '".
(* Notation "f '" := (Derive f) : RFun_scope (default interpretation) *)

(** 在VFCS库中，提供了二阶常系数齐次线性微分方程的形式化理论 *)

Print HomoLDE2.
(* 
   Record Eqn : Set := Build_Eqn { a : R;  b : R }.
   Definition isSolution : Eqn -> (R -> R) -> Prop.
   Definition D : Eqn -> R.
   Module Dgt0
   Module Deq0
   Module Dlt0
 *)

(** Δ > 0 的情形 *)
Print HomoLDE2.Dgt0.
(* 
   Definition r1 : Eqn -> R.
   Definition r2 : Eqn -> R.
   Definition y : Eqn -> R -> R -> R -> R.
   Parameter y_spec :
     forall e : Eqn, D e > 0 -> forall c1 c2 : R, isSolution e (y e c1 c2).
 *)
Print HomoLDE2.Dgt0.r1. (* 特征方程的第1个特征根 *)
(* 
   Dgt0.r1 = fun e : Eqn => (- e.a + sqrt (D e)) / 2
   : Eqn -> R
 *)
Print HomoLDE2.Dgt0.y.  (* 方程的解 *)
(* 
   Dgt0.y =
     fun (e : Eqn) (c1 c2 x : R) => c1 * exp (Dgt0.r1 e * x) + c2 * exp (Dgt0.r2 e * x)
     : Eqn -> R -> R -> R -> R
 *)

(** Δ = 0 的情形 *)
Print HomoLDE2.Deq0.
(* 
   Definition r : Eqn -> R.
   Definition y : Eqn -> R -> R -> R -> R.
   Parameter y_spec :
     forall e : Eqn, D e = 0 -> forall c1 c2 : R, isSolution e (y e c1 c2).
 *)
Print HomoLDE2.Deq0.y.  (* 方程的解 *)
(* 
   Deq0.y =
   fun (e : Eqn) (c1 c2 x : R) => (c1 + c2 * x) * exp (Deq0.r e * x)
     : Eqn -> R -> R -> R -> R
 *)

(** Δ < 0 的情形，两个共轭的复根 *)
Print HomoLDE2.Dlt0.
(* 
   Definition r1 : Eqn -> C.
   Definition r2 : Eqn -> C.
   Definition y : Eqn -> R -> R -> R -> R.
   Parameter y_spec :
     forall e : Eqn, D e < 0 -> forall c1 c2 : R, isSolution e (y e c1 c2).
 *)


(** * RLC二阶电路的微分方程 *)

(* 使用Axiom的做法。优点：清晰、灵活；缺点：中间变量(uR,uL,i)无法消去 *)
Section uC_by_uS'.

  (* 电阻、电感、电容 *)
  Variable r L C : R.
  Hypotheses r_gt0 : r > 0.
  Hypotheses L_gt0 : L > 0.
  Hypotheses C_gt0 : C > 0.
  (* 电压源电压、电容器电压 *)
  Variable uS uC : R -> R.

  (* 中间变量：电阻器电压、电感器电压、串联电路的电流 *)
  Variable uR uL i : R -> R.

  (** 电容模型：电流是电压变化率乘以电容 *)
  Axiom C_MODEL : forall t, i t = C * (uC ' t).
  (** 电感模型：电压是电流变化率乘以电感 *)
  Axiom L_MODEL : forall t, uL t = L * (i ' t).
  (** 欧姆定律：电阻的电压等于电阻乘以电流 *)
  Axiom Ohm_MODEL : forall t, uR t = r * i t.

  (** KVL定律：总压降等于总压升 *)
  Axiom KVL_MODEL' : forall t, uR t + uL t + uC t = uS t.

  (** 以 uS(t) 为激励，以 uC(t) 为响应的微分方程 *)
  Theorem uC_by_uS' : forall t,
      uC '' t + (r/L) * uC ' t  + (/(L*C)) * uC t = (/(L*C)) * uS t.
  Proof.
    intros. rewrite <- KVL_MODEL'.
    rewrite Ohm_MODEL. rewrite L_MODEL. rewrite C_MODEL.
    field_simplify_eq; [|lra].
    (* 此处的 move2h 可以将一个项移动到头部，还有对应的 move2t 策略 *)
    move2h (uC t). move2h (uC t). f_equal.
    rewrite commutative. f_equal.
    move2h L. f_equal.
    rewrite commutative. rewrite <- Derive_scal. apply Derive_ext.
    intros. rewrite C_MODEL. auto.
  Qed.
End uC_by_uS'.

Check uC_by_uS'.
(* 
  : forall r L C : R,
  L > 0 ->
  C > 0 ->
  forall uS uC : R -> R,
  (R -> R) ->
  (R -> R) ->
  (R -> R) ->
  forall t : R, (uC ') ' t + r / L * uC ' t + / (L * C) * uC t = / (L * C) * uS t
 *)

(* 使用 Definition 的做法，更简洁 *)
Section uC_by_uS.
  
  (* 电阻、电感、电容 *)
  Variable r L C : R.
  Hypotheses r_gt0 : r > 0.
  Hypotheses L_gt0 : L > 0.
  Hypotheses C_gt0 : C > 0.
  (* 电压源电压、电容器电压 *)
  Variable uS uC : R -> R.

  (** 电容模型：电流是电压变化率乘以电容 *)
  Definition i (t : R) := C * (uC ' t).
  (** 电感模型：电压是电流变化率乘以电感 *)
  Definition uL (t : R) := L * (i ' t).
  (** 欧姆定律：电阻的电压等于电阻乘以电流 *)
  Definition uR (t : R) := r * i t.

  (** KVL定律：总压降等于总压升 *)
  Axiom KVL_MODEL : forall t, uR t + uL t + uC t = uS t.

  (** 以 uS(t) 为激励，以 uC(t) 为响应的微分方程 *)
  Theorem uC_by_uS : forall t,
      uC '' t + (r/L) * uC ' t  + (/(L*C)) * uC t = (/(L*C)) * uS t.
  Proof.
    intros. rewrite <- KVL_MODEL. unfold uR, uL, i.
    field_simplify_eq; [|lra].
    (* move2h策略可将一个项移动到头部。也有类似的 move2t 策略 *)
    move2h (uC t). move2h (uC t). f_equal.
    rewrite commutative. f_equal.
    move2h L. f_equal.
    rewrite commutative. rewrite <- Derive_scal. auto.
  Qed.
End uC_by_uS.

Check uC_by_uS.
(* 
uC_by_uS
  : forall r L C : R,
  L > 0 ->
  C > 0 ->
  forall (uS uC : R -> R) (t : R),
  (uC ') ' t + r / L * uC ' t + / (L * C) * uC t = / (L * C) * uS t
 *)


(** * RLC二阶电路的零输入响应 *)
Section ZIR.
  
  (* 电阻、电感、电容 *)
  Variable r L C : R.
  Hypotheses r_gt0 : r > 0.
  Hypotheses L_gt0 : L > 0.
  Hypotheses C_gt0 : C > 0.
  (* 电容器电压 *)
  Variable uC : R -> R.

  (** 零输入响应的微分方程 *)
  Theorem uC_ZIR : forall t, uC '' t + (r/L) * uC ' t  + (/(L*C)) * uC t = 0.
  Proof.
    intros. rewrite uC_by_uS with (uS := fun _ => 0); auto. lra.
  Qed.

  (* 令 2α = (r/L)，ω0 = 1/√(LC)。称 α 为衰减常数，ω0 为谐振角频率 *)
  Definition alpha : R := (r/L)/2.  Notation α := alpha.
  Definition omega0 : R := / (sqrt (L * C)). Notation ω0 := omega0.

  (* uC_ZIR 的另一种形式 *)
  Fact uC_ZIR2 : forall t, uC '' t + 2 * α * uC ' t + ω0² * uC t = 0.
  Proof.
    intros. pose proof (uC_ZIR t).
    unfold α, ω0. rewrite <- H. f_equal. f_equal. lra.
    f_equal. ra.
    (* 若不使用 ra 策略，可使用以下手动证明 *)
    Back.
    Fail lra. (* 说明 lra 无效 *)
    rewrite Rsqr_inv'. rewrite Rsqr_sqrt. auto.
    Fail lra. (* 说明 lra 无法解决 L > 0, C > 0 |- 0 <= L * C *)
    apply Rmult_le_pos; lra.
  Qed.

  (* 关于 α, ω0 的一些基本事实，后面会用到 *)
  Fact α_gt0 : α > 0.
  Proof. unfold α. assert (0 < 2); ra. Qed.

  Fact ω0_gt0 : ω0 > 0.
  Proof. unfold ω0. assert (0 < 2); ra. Qed.

  (* 建立微分方程对象，以便使用 HomoLDE2 的理论 *)
  Definition eq1 : Eqn := Build_Eqn (2 * α) ω0².

  (* 验证 uC 是 eq1 的解 *)
  Lemma eq1_spec : isSolution eq1 uC.
  Proof.
    unfold isSolution. simpl.
    feq. pose proof (uC_ZIR2 x). auto.
  Qed.

  (** ** 分析R、L、C不同取值时的零输入响应 u(t), i(t) *)

  (** *** (1) α > ω0，即 R² > 4L/C，过阻尼情况(overdamped, OD) *)
  Section OD.

    (* 假设 α > ω0 *)
    Hypotheses Hgt : α > ω0.

    (* 等价形式：R² > 4L/C *)
    Lemma Hgt' : r² > 4 * L / C.
    Proof.
      unfold α, ω0 in Hgt.
      replace (r / L / 2) with (r / (2 * L)) in Hgt; ra.
      assert (0 < 2); ra.
      assert (r > (2 * L) / sqrt (L * C)).
      { apply Rmult_gt_reg_r with (r := /(2 * L)); ra.
        replace (2 * L / sqrt (L * C) / (2 * L)) with (/ sqrt (L * C)); ra. }
      apply Rsqr_mono_gt0 in H0; ra.
      rewrite Rsqr_sqrt in H0; ra.
      replace (2² * L² / (L * C)) with (4 * L / C) in H0; ra.
    Qed.

    (* Δ > 0 *)
    Lemma delta_gt0 : D eq1 > 0.
    Proof.
      unfold D. simpl.
      assert (α * α - ω0 * ω0 > 0); ra.
      pose proof α_gt0. pose proof ω0_gt0. ra.
    Qed.
    
    (* 特征根是两个不相等的负实根，-α1, -α2 *)
    Let p1 := - α + sqrt (α² - ω0²).
    Let p2 := - α - sqrt (α² - ω0²).
    Let α1 := -p1.
    Let α2 := -p2.

    (* 验证特征根表达式 *)
    Lemma p1_eq_OD : p1 = HomoLDE2.Dgt0.r1 eq1.
    Proof.
      unfold Dgt0.r1, D, p1, eq1. simpl.
      replace (sqrt (2 * α * (2 * α) - 4 * ω0²)) with (2 * sqrt (α² - ω0²)); ra.
      replace (2² * α² - 4 * ω0²) with (2² * (α² - ω0²)); ra.
      rewrite sqrt_mult_alt; ra. f_equal.
      assert (0 < 2); ra.
    Qed.

    Lemma p2_eq_OD : p2 = HomoLDE2.Dgt0.r2 eq1.
    Proof.
      unfold Dgt0.r2, D, p2, eq1. simpl.
      replace (sqrt (2 * α * (2 * α) - 4 * ω0²)) with (2 * sqrt (α² - ω0²)); ra.
      replace (2² * α² - 4 * ω0²) with (2² * (α² - ω0²)); ra.
      rewrite sqrt_mult_alt; ra. f_equal.
      assert (0 < 2); ra.
    Qed.

    (* α2 - α1 <> 0，后文会用到 *)
    Fact α2_minus_α1_neq0 : α2 - α1 <> 0.
    Proof.
      unfold α2, α1, p1,p2. intro.
      ring_simplify in H.
      assert (α² - ω0² > 0); ra.
      apply Rgt_minus. apply Rsqr_mono_gt0; auto.
      apply ω0_gt0. apply α_gt0.
      assert (sqrt (α² - ω0²) > 0); ra.
    Qed.

    (* 待定系数 C1,C2 *)
    Variable C1 C2 : R.

    (* u(t) 的解（含待定系数） *)
    Let uODX (t : R) : R := C1 * exp (p1 * t) + C2 * exp (p2 * t).
    
    Lemma uODX_spec : isSolution eq1 uODX.
    Proof.
      pose proof (Dgt0.y_spec eq1 delta_gt0 C1 C2).
      unfold uODX. unfold Dgt0.y in H.
      rewrite p1_eq_OD, p2_eq_OD. auto.
    Qed.

    (* uODX 的导函数的等价形式，后文会用用到 *)
    Lemma d_uODX_eq :
      uODX ' = fun t => C1 * p1 * exp (p1 * t) + C2 * p2 * exp (p2 * t).
    Proof.
      unfold uODX. extensionality t.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (* 设电路的初始状态如下 *)
    Variable U0 : R.
    Hypotheses uODX_0 : uODX 0 = U0.  (* 表示 u(0+)。todo: 此处需要改进 *)
    Hypotheses i_0 : i C uODX 0 = 0. (* 表示 i(0+) *)

    (* 确定 C1, C2 的值 *)
    Fact C1C2_eq1_OD : C1 + C2 = U0.
    Proof. unfold uODX in uODX_0. ra. Qed.

    Fact C1C2_eq2_OD : C1 * p1 + C2 * p2 = 0.
    Proof.
      unfold i in i_0.
      assert (uODX ' 0 = 0); ra.
      rewrite d_uODX_eq in H. ra.
    Qed.

    (* 由上述两个方程解出 C1,C2 *)
    Lemma C1_eq_OD : C1 = (U0 * α2) / (α2 - α1).
    Proof.
      pose proof C1C2_eq1_OD. pose proof C1C2_eq2_OD.
      assert (C2 = U0 - C1); ra.
      assert (C1 * p1 + (U0 - C1) * p2 = 0); ra.
      assert (C1 * (p1 - p2) + U0 * p2 = 0); ra.
      field_simplify_eq. unfold α1,α2; ra. apply α2_minus_α1_neq0.
    Qed.

    Lemma C2_eq_OD : C2 = (- U0 * α1) / (α2 - α1).
    Proof.
      pose proof C1C2_eq1_OD. pose proof C1C2_eq2_OD.
      assert (C1 = U0 - C2); ra.
      assert ((U0 - C2) * p1 + C2 * p2 = 0); ra.
      assert (C2 * (p2 - p1) + U0 * p1 = 0); ra.
      field_simplify_eq. unfold α1,α2; ra. apply α2_minus_α1_neq0.
    Qed.

    (* u(t) 的解（不含待定系数） *)
    Definition uOD (t : R) : R :=
      (U0 / (α2 - α1)) * (α2 * exp (- α1 * t) - α1 * exp (- α2 * t)).

    (* 验证 uOD 与 uODX 相等 *)
    Lemma uOD_spec : uOD = uODX.
    Proof.
      unfold uOD, uODX. rewrite C1_eq_OD, C2_eq_OD. extensionality t.
      field_simplify_eq. unfold α2, α1. ra. apply α2_minus_α1_neq0.
    Qed.

    (* i(t) 的解 *)
    Definition iOD (t : R) : R :=
      (- (α1 * α2 * C * U0) / (α2 - α1)) * (exp (- α1 * t) - exp (- α2 * t)).

    (* 验证 i = C * u' *)
    Lemma iOD_spec : iOD = C s* uOD '.
    Proof.
      (* 首先，uOD 改写为 uODX *)
      rewrite uOD_spec.
      (* 利用 uODX 的导数 *)
      rewrite d_uODX_eq.
      (* 化简 *)
      unfold iOD. rewrite C1_eq_OD, C2_eq_OD.
      feq. field_simplify_eq. unfold α1, α2. ra.
      apply α2_minus_α1_neq0.
    Qed.
  End OD.


  (** *** (2) α = ω0，即 R² = 4L/C，临界阻尼情况(critical damping, CD) *)
  Section CD.

    (* 假设 α = ω0 *)
    Hypotheses Heq : α = ω0.

    (* 等价形式：R² = 4L/C *)
    Lemma Heq' : r² = 4 * L / C.
    Proof.
      unfold α, ω0 in Heq.
      replace (r / L / 2) with (r / (2 * L)) in Heq; ra.
      assert (0 < 2); ra.
      assert (r = (2 * L) / sqrt (L * C)).
      { apply Rdiv_eq_reg_r with (r := (2 * L)); ra. rewrite Heq; ra. }
      rewrite H0; ra. rewrite Rsqr_sqrt; ra.
    Qed.

    (* Δ = 0 *)
    Lemma delta_eq0 : D eq1 = 0.
    Proof.
      unfold D. simpl. rewrite Heq. ra.
    Qed.

    (* 特征根是相等的负实根，即 -α *)
    Let p := -α.

    (* 验证特征根表达式 *)
    Lemma p_eq_CD : p = HomoLDE2.Deq0.r eq1.
    Proof.
      unfold Deq0.r, D, p, eq1. simpl. ra.
    Qed.

    (* 待定系数 C1,C2 *)
    Variable C1 C2 : R.

    (* u(t) 的解（含待定系数） *)
    Let uCDX (t : R) : R := (C1 + C2 * t) * exp (p * t).
    
    Lemma uCDX_spec : isSolution eq1 uCDX.
    Proof.
      pose proof (Deq0.y_spec eq1 delta_eq0 C1 C2).
      unfold uCDX. unfold Deq0.y in H.
      rewrite p_eq_CD. auto.
    Qed.

    (* uCDX 的导函数的等价形式，后文会用用到 *)
    Lemma d_uCDX_eq :
      uCDX ' = fun t => (C1 * p + C2 + C2 * p * t) * exp (p * t).
    Proof.
      unfold uCDX. extensionality t.
      apply is_derive_unique. auto_derive; auto. ring.
    Qed.

    (* 设电路的初始状态如下 *)
    Variable U0 : R.
    Hypotheses uCDX_0 : uCDX 0 = U0.  (* 表示 u(0+)。todo: 此处需要改进 *)
    Hypotheses i_0 : i C uCDX 0 = 0. (* 表示 i(0+) *)

    (* 确定 C1, C2 的值 *)
    Lemma C1_eq_CD : C1 = U0.
    Proof.
      unfold uCDX in uCDX_0. ra.
    Qed.

    Lemma C2_eq_CD : C2 = U0 * α.
    Proof.
      unfold i in i_0. rewrite d_uCDX_eq in i_0. rewrite C1_eq_CD in i_0. ra.
      assert (U0 * p + C2 = 0); ra. unfold p in H. ra.
    Qed.

    (* u(t) 的解（不含待定系数） *)
    Definition uCD (t : R) : R := U0 * (1 + α * t) * exp (- α * t).

    (* 验证 uCD 与 uCDX 相等 *)
    Lemma uCD_spec : uCD = uCDX.
    Proof.
      unfold uCD, uCDX. rewrite C1_eq_CD, C2_eq_CD. extensionality t.
      field_simplify_eq. unfold α. ra.
    Qed.

    (* i(t) 的解 *)
    Definition iCD (t : R) : R := - C * U0 * α² * t * exp (- α * t).

    (* 验证 i = C * u' *)
    Lemma iCD_spec : iCD = C s* uCD '.
    Proof.
      (* 首先，uCD 改写为 uCDX *)
      rewrite uCD_spec.
      (* 利用 uCDX 的导数 *)
      rewrite d_uCDX_eq.
      (* 化简 *)
      unfold iCD. rewrite C1_eq_CD, C2_eq_CD. feq.
      field_simplify_eq. unfold p. ra.
    Qed.
  End CD.


  (** *** (3) α < ω0，即 R² < 4L/C，欠阻尼情况(underdamped, UD) *)
  Section UD.

    (* 假设 α < ω0 *)
    Hypotheses Hlt : α < ω0.

    (* 等价形式：R² < 4L/C *)
    Lemma Hlt' : r² < 4 * L / C.
    Proof.
      unfold α, ω0 in Hlt.
      replace (r / L / 2) with (r / (2 * L)) in Hlt; ra.
      assert (0 < 2); ra.
      assert (r < (2 * L) / sqrt (L * C)).
      { apply Rmult_lt_reg_r with (r := /(2 * L)); ra.
        replace (2 * L / sqrt (L * C) / (2 * L)) with (/ sqrt (L * C)); ra. }
      apply Rsqr_mono_gt0 in H0; ra.
      rewrite Rsqr_sqrt in H0; ra.
      replace (2² * L² / (L * C)) with (4 * L / C) in H0; ra.
    Qed.

    (* Δ < 0 *)
    Lemma delta_lt0 : D eq1 < 0.
    Proof.
      unfold D. simpl.
      assert (α * α - ω0 * ω0 < 0); ra.
      pose proof α_gt0. pose proof ω0_gt0. ra.
    Qed.
    
    (* 特征根是一对共轭的复根 *)
    Let ωd : R := sqrt (ω0² - α²).
    Let p1 : Complex.C := - α +i ωd. 
    Let p2 : Complex.C := - α +i (-ωd).

    (* ωd > 0，在后文会用到 *)
    Lemma ωd_gt0 : ωd > 0.
    Proof.
      unfold ωd.
      assert (ω0² - α² > 0); ra.
      apply Rsqr_mono_gt0 in Hlt; ra.
      apply α_gt0. apply ω0_gt0.
    Qed.

    (* 验证特征根表达式 *)
    Lemma p1_eq_UD : p1 = HomoLDE2.Dlt0.r1 eq1.
    Proof.
      unfold Dlt0.r1, Dlt0.alpha, Dlt0.beta, D, p1, ωd, eq1. simpl. f_equal; ra.
      replace (- (2² * α² - 4 * ω0²)) with (2² * (ω0² - α²)); ra.
      rewrite sqrt_mult_alt; ra.
      replace (| 2 |) with 2; ra. assert (0 < 2); ra.
    Qed.

    Lemma p2_eq_UD : p2 = HomoLDE2.Dlt0.r2 eq1.
    Proof.
      unfold Dlt0.r2, Dlt0.alpha, Dlt0.beta, D, p2, ωd, eq1. simpl. f_equal; ra.
      replace (- (2² * α² - 4 * ω0²)) with (2² * (ω0² - α²)); ra.
      rewrite sqrt_mult_alt; ra.
      replace (| 2 |) with 2; ra. assert (0 < 2); ra.
    Qed.

    (* 待定系数 C1,C2 *)
    Variable C1 C2 : R.

    (* u(t) 的解（含待定系数） *)
    Let uUDX (t : R) : R := exp (- α * t) * (C1 * cos (ωd * t) + C2 * sin (ωd * t)).
    
    Lemma uUDX_spec : isSolution eq1 uUDX.
    Proof.
      pose proof (Dlt0.y_spec eq1 delta_lt0 C1 C2).
      replace (Dlt0.y eq1 C1 C2) with uUDX in H; auto.
      unfold uUDX. unfold Dlt0.y, Dlt0.alpha, Dlt0.beta, D, ωd. simpl.
      feq. ring_simplify.
      replace (- (2 * α / 2 * x)) with (- (α * x)); ra. ring_simplify.
      replace (- (2² * α² - 4 * ω0²)) with (2² * (ω0² - α²)); ra.
      rewrite sqrt_mult_alt; ra.
      replace (| 2 | * sqrt (ω0² - α²) / 2 * x) with (sqrt (ω0² - α²) * x); ra.
      replace (| 2 |) with 2; ra. assert (0 < 2); ra.
    Qed.

    (* uUDX 的导函数的等价形式，后文会用用到 *)
    Lemma d_uUDX_eq :
      uUDX ' = fun t => (-α*C1 + C2*ωd) * exp (-α*t) * cos(ωd*t) +
                        (-α*C2 - C1*ωd) * exp (-α*t) * sin(ωd*t).
    Proof.
      unfold uUDX. extensionality t.
      apply is_derive_unique. auto_derive; auto. lra.
    Qed.

    (* 设电路的初始状态如下 *)
    Variable U0 : R.
    Hypotheses uUDX_0 : uUDX 0 = U0.  (* 表示 u(0+)。todo: 此处需要改进 *)
    Hypotheses i_0 : i C uUDX 0 = 0. (* 表示 i(0+) *)

    (* 确定 C1, C2 的值 *)
    Fact C1_eq_UD : C1 = U0.
    Proof. unfold uUDX in uUDX_0. ra. Qed.

    Fact C2_eq_UD : C2 = (α / ωd) * U0.
    Proof.
      unfold i in i_0.
      assert (uUDX ' 0 = 0); ra.
      rewrite d_uUDX_eq in H. ra. rewrite C1_eq_UD in H. field_simplify_eq; ra.
      pose proof ωd_gt0; ra.
    Qed.

    (* u(t) 的解（不含待定系数） *)
    Definition uUD (t : R) : R :=
      (ω0 / ωd) * U0 * exp (- α * t) * cos (ωd * t - atan (α / ωd)).

    (* 验证 uUD 与 uUDX 相等 *)
    Lemma uUD_spec : uUD = uUDX.
    Proof.
      unfold uUD, uUDX. rewrite C1_eq_UD, C2_eq_UD. feq. ring_simplify.
      repeat (move2h (exp (- (α * x)))). repeat (move2h U0).
      pose proof ω0_gt0. pose proof ωd_gt0.
      f_equal; f_equal; f_equal.
      - replace (cos (atan (α / ωd))) with (ωd / ω0); ra. rewrite cos_atan.
        replace (1 + (α / ωd)²) with ((ω0 / ωd)²); ra. rewrite Rabs_right; ra.
        replace ωd² with (ω0² - α²); ra. unfold ωd. rewrite Rsqr_sqrt; ra.
      - replace (sin (atan (α / ωd))) with (α / ω0); ra. rewrite sin_atan.
        replace (1 + (α / ωd)²) with ((ω0 / ωd)²); ra. rewrite Rabs_right; ra.
        replace ωd² with (ω0² - α²); ra. unfold ωd. rewrite Rsqr_sqrt; ra.
    Qed.

    (* i(t) 的解 *)
    Definition iUD (t : R) : R :=
      - (ω0² / ωd) * C * U0 * exp (- α * t) * sin (ωd * t).

    (* 验证 i = C * u' *)
    Lemma iUD_spec : iUD = C s* uUD '.
    Proof.
      (* 首先，uUD 改写为 uUDX *)
      rewrite uUD_spec.
      (* 利用 uUDX 的导数 *)
      rewrite d_uUDX_eq.
      (* 化简 *)
      unfold iUD. rewrite C1_eq_UD, C2_eq_UD. pose proof ωd_gt0.
      feq. field_simplify_eq; ra.
      replace ωd² with (ω0² - α²); ra. unfold ωd. rewrite Rsqr_sqrt; ra.
    Qed.
  End UD.


  (** *** (4) α = 0，即 R = 0，无阻尼情况(no damping, ND)，它也是一种欠阻尼情形 *)
  Section ND.

    (* 假设 α = 0 *)
    Hypotheses Heq0 : α = 0.

    (* 等价形式：R = 0 *)
    Lemma Heq0' : r = 0.
    Proof.
      unfold α in Heq0.
      replace (r / L / 2) with (r * / (2 * L)) in Heq0 by ra.
      apply Rmult_integral in Heq0. destruct Heq0; ra.
      assert (2 * L > 0); ra.
      assert (/ (2 * L) > 0); ra.
    Qed.

    (* Δ < 0 *)
    Lemma delta_lt0_ND : D eq1 < 0.
    Proof.
      unfold D. simpl. rewrite Heq0. ra.
      pose proof ω0_gt0. ra.
    Qed.

    (* 设电路的初始状态如下 *)
    Variable U0 : R.  (* 表示 u(0+)。todo: 此处需要改进 *)
    (* Print uUD. *)
    (* Check uUD U0. *)
    
    (* u(t) 的解（不含待定系数） *)
    Definition uND (t : R) : R := U0 * cos (ω0 * t).

    (* 验证 uND 与 uUD 相等 *)
    Lemma uND_spec : uND = uUD U0.
    Proof.
      unfold uND, uUD. feq. pose proof ω0_gt0. rewrite Heq0; ra.
      rewrite Rabs_right; ra.
    Qed.

    (* i(t) 的解 *)
    Definition iND (t : R) : R := - C * ω0 * U0 * sin (ω0 * t).

    (* 验证 iND = iUD *)
    Lemma iND_spec : iND = iUD U0.
    Proof.
      unfold iND, iUD. feq. pose proof ω0_gt0. rewrite Heq0; ra.
      rewrite Rabs_right; ra.
    Qed.
  End ND.

End ZIR.
