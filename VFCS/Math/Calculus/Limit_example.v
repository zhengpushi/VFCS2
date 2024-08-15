
(* 
   问题：
   在一个有关向量的证明时，讲义中提到要将导数转化为而极限，而当展开至极限时，
   总是需要一个 h <> 0 的证明，这个问题很普遍，如何解决？

   date : 2024.06.25
 *)

Require Import Logic.FunctionalExtensionality.
Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* 给定函数 f(x) = 2 * x *)
Definition f : R -> R := fun x => 2 * x.

(* 证明 f(x) 的导数是 fun x => 2 *)
Lemma ex1 : Derive f = fun x => 2.
Proof.
  unfold f. extensionality x. apply is_derive_unique.
  auto_derive; auto. lra.
Qed.

(* 不直接证明，而是展开为极限的形式。
   之所以要展开为极限，是因为有时候极限形式可以做更多的化简 *)
Lemma ex2 : Derive f = fun x => 2.
Proof.
  unfold f. unfold Derive. extensionality x.
  (* 利用极限的性质来证明 *)
  rewrite Lim_ext with (f:=fun h=> 2).
  - rewrite Lim_const. auto.
  - intros y. field_simplify_eq. auto.
    (* 无法证明 y <> 0，这看起来很普遍，如何看待这个待证目标？ *)
Abort.

(* 找到 Lim 在 posreal 上的等价定义，避免 y <> 0 的前提 *)
Section Lim_eq.
  Variable f : R -> R.
  Print Lim.
  (* 
fun (f : R -> R) (x : Rbar) => Lim_seq (fun n : nat => f (Rbar_loc_seq x n))
     : (R -> R) -> Rbar -> Rbar *)

  Print Lim_seq.
  (* 
Lim_seq =
fun u : nat -> R =>
Rbar_div_pos (Rbar_plus (LimSup_seq u) (LimInf_seq u)) {| pos := 2; cond_pos := Rlt_R0_R2 |}
     : (nat -> R) -> Rbar
   *)
  
  Print Rbar_loc_seq.
  (* 
Rbar_loc_seq =
fun (x : Rbar) (n : nat) =>
match x with
| Finite x0 => x0 + / (INR n + 1)
| p_infty => INR n
| m_infty => - INR n
end
     : Rbar -> nat -> R
   *)
End Lim_eq.
    
Lemma ex2 : Derive f = fun x => 2.
Proof.
  unfold f. unfold Derive. extensionality x.
  (* Search Lim. *)
  (* 使用 Lim_ext_loc，而不是 Lim_ext，因为需要去心 *)
  rewrite Lim_ext_loc with (f := fun h => 2).
  - rewrite Lim_const. auto.
  - (* 可直接计算 *)
    (* cbv. *)
    (* 还可手动展开 *)
    unfold Rbar_locally'. unfold locally'. unfold within.
    unfold locally. unfold ball. simpl. unfold AbsRing_ball.
    (* 现在就是熟悉的 epsilon 语言了，并且由于epsilon与最终目标无关，可任意给定 *)
    exists posreal_one. intros. field; auto.
Qed.
