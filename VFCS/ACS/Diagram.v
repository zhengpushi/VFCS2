(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 对方框图、结构图、传递函数等的形式化，以便完成数学模型的建立
  author    : Zhengpu Shi
  date      : 2021.12
  
  ref       :
  1. Control Systems Engineering by Norman S. Nise
  2. 自动控制原理，卢京潮
  
  remark    :
  1. 参考 1.4 节，分析和设计目标，天线位置控制系统的案例
    (a). 几个不同阶段的图：
      system concept    系统概念
      detailed layout   详细布局
      schematic         原理图
      functional block diagram  功能方框图，只有物理层意义上的文字描述
      block diagram     方框图，数学模型
  2. 参考 1.5 节，The Design Process
    控制系统的设计流程
    1) 根据"需求"来决定"物理系统和规范"
    2) 绘制"功能方框图"
    3) 将物理系统表示为"原理图"
    4) 根据原理图来获得"方框图"，"信号流图"，"状态空间"表示
    5) 如果是多个方框，约简到一个"单一方框"或"闭环系统"
    6) 分析，设计，测试。
  3. 一些名词对照
    外文版的书                 中文版的书    统一命名
    Functional Block Diagram  方框图       FBD    
    Block Diagram             结构图       BD
    Summing junction          比较点       Summing
    Block                     方框         Block
*)

Require Import Ascii String.
Open Scope string.

Require Import List.
Import ListNotations.


(* ######################################################################### *)
(** * Functional Block Diagram *)

(* 此时，方框只有文字描述，无数学函数。
  尽管如此，系统结构已经有了，可以做一些算法研究 *)

(** 功能方框图 
  1. 包含的部件
    方框，多个
    比较点，多个
    连线，多个
  2. 规则
    BD中必须只有1个入口和1个出口；
    比较点是多输入1输出，每个输入有正负两种极性；
*)
Module FunctionalBlockDiagram.

  (** 方向 *)
  Inductive Direction := DI | DO.
  
  (** 汇合点输入信号的符号 *)
  Inductive Sign := SPos | SNeg.
  
  (** 连接点 *)
  Inductive Joint := joint (n:nat) (d : Direction).
  
  (** 方框 *)
  Record Block := mkBlock {
    Bname : string;   (* 一般不为空 *)
    Bin : Joint;
    Bout : Joint
  }.
  
  (** 信号线、连线 *)
  Record Line := mkLine {
    Lname : string;   (* 可为空 *)
    Lin : Joint;
    Lout : Joint
  }.
  
  (** 比较点，汇合点 *)
  Record Summing := mkSumming {
    Sin : list (Joint * Sign);
    Sout : Joint
  }.
  
  (** 方框图 *)
  Record BD := mkBD {
    BDname : string;
    BDblks : list Block;
    BDsums : list Summing;
    BDlines : list Line;
    BDinput : Joint;      (** 入口 *)
    BDoutput : Joint      (** 出口 *)
  }.
  
  (** 继续做一些探索
    1. 找出所有前向通道，从入口到出口
    2. 找出所有回路？将来 melson 公式需要
   *)
  
  (** list (Joint * Sign) to list Joint *)
  Definition js2j_lst (l : list (Joint * Sign)) : list Joint :=
    map (fun (js : Joint * Sign) => let (j,_) := js in j) l.
  
  (** 类型定义：两点连接 *)
  Definition C2 := prod Joint Joint.
  
  (** 两点连接的规范 *)
  
  (** 情形1，由 Line 生成 *)
  Definition C2spec_line (bd:BD) (c2:C2) : Prop :=
    let (j0,j1) := c2 in
    exists (l:Line), In l (BDlines bd) /\ Lin l = j0 /\ Lout l = j1.

  (** 情形2，由 Block 生成 *)
  Definition C2spec_block (bd:BD) (c2:C2) : Prop :=
    let (j0,j1) := c2 in
    exists (b:Block), In b (BDblks bd) /\ Bin b = j0 /\ Bout b = j1.

  (** 情形3，由 Summing 生成 *)
  Definition C2spec_sum (bd:BD) (c2:C2) : Prop :=
    let (j0,j1) := c2 in
    exists (s:Summing), let j0s := js2j_lst (Sin s) in
      In s (BDsums bd) /\ In j0 j0s /\ Sout s = j1.
  
  (** 几种情形，只要满足一种即可 *)
  Definition C2spec (bd:BD) (c2:C2) : Prop :=
    C2spec_line bd c2 \/ C2spec_block bd c2 \/ C2spec_sum bd c2.
  
  (** 计算两点连接 *)
  
  (** 计算 BD 中所有 line 构成的 C2 *)
  Definition bdC2_line (bd : BD) : list C2 :=
    map (fun l:Line => (Lin l, Lout l)) (BDlines bd).
  
  Lemma bdC2_line_correct : forall bd : BD,
    forall c2, In c2 (bdC2_line bd) -> C2spec_line bd c2.
  Proof.
    destruct bd. intros [j0 j1] H. destruct BDlines0; simpl in *; try easy.
    destruct H.
    - exists l. inversion H; subst. split; auto.
    - apply in_map_iff in H. inversion H. inversion H0. inversion H1.
      exists x. split; auto.
  Qed.
  
  (** 计算 BD 中所有 block 构成的 C2 *)
  Definition bdC2_blk (bd : BD) : list C2 :=
    map (fun b:Block => (Bin b, Bout b)) (BDblks bd).
  
  Lemma bdC2_blk_correct : forall bd : BD,
    forall c2, In c2 (bdC2_blk bd) -> C2spec_block bd c2.
  Proof.
    destruct bd. intros [j0 j1] H. destruct BDblks0; simpl in *; try easy.
    destruct H.
    - exists b. inversion H; subst. split; auto.
    - apply in_map_iff in H. inversion H. inversion H0. inversion H1.
      exists x. split; auto.
  Qed.
  
  (** 计算 BD 中所有 Summing 构成的 C2 *)
  Definition bdC2_sum (bd : BD) : list C2 :=
    concat
      (map (fun s : Summing => let j1 := Sout s in
        map (fun js : Joint * Sign => let (j0, _) := js in (j0, j1))
          (Sin s))
        (BDsums bd)).
  
  (* 证明思路，以一个简单的数据结构为例 *)
  Module Example_for_C2.
  
    (** 某个节点，记录了 n 个输入 和 1 个输出 *)
    Record Junction := mkJunction {
      Jins : list nat;      (* 输入端口的列表 *)
      Jout : nat            (* 输出端口 *)
    }.

    Example j1 := mkJunction [1;2] 3.
    Example j2 := mkJunction [5;6] 7.

    (** 连线：在同一个节点中的 (输入,输出) 对偶构成一条连线 *)
    (* 例如， [(1,3);(2,3)] 是 j1 的所有连线的列表。*)
    (* Compute map (fun i => (i, (Jout j1))) (Jins j1). *)

    (** 定义规范，检查任意自然数对 (i,j) 能否构成 Line ？*) 
    Definition IsLine (n0 n1 : nat) (j : Junction) : Prop :=
      In n0 (Jins j) /\ n1 = Jout j.

    (** 定义计算函数，并证明该函数计算完的结果都满足规范 *)
    Definition findLines (j : Junction) : list (nat * nat) :=
      map (fun i => (i, (Jout j))) (Jins j).

    Lemma findLines_ok : forall j : Junction,
      let lines := findLines j in
        forall xy, In xy lines -> (let (x,y) := xy in IsLine x y j).
    Proof.
      intros [jins jout]. simpl. induction jins.
      - intros. cbv in *. easy.
      - intros [x y]. simpl in *. intros. destruct H.
        + unfold IsLine in *. simpl in *. inversion H; subst. split; auto.
        + cbn in *. apply IHjins in H. unfold IsLine in *. simpl in *.
          destruct H; auto.
    Qed.
    
  End Example_for_C2.
  
  
  (** 两个点之间是否是连通的？*)
  (** 路径 *)
  (** 找出所有前向通路 *)
  
  (** example in Fig 1.8 *)
  Section AntennaPositionControlSystem.
  
    (* 所有的连接点 *)
    Let  j0 := joint  0 DO.   (* 入口处 *)
    Let  j1 := joint  1 DI.   (* Input transducer入口 *)
    Let  j2 := joint  2 DO.   (* Input transducer出口 *)
    Let  j3 := joint  3 DI.   (* Summing junction入口1 *)
    Let  j4 := joint  4 DI.   (* Summing junction入口2 *)
    Let  j5 := joint  5 DO.   (* Summing junction出口 *)
    Let  j6 := joint  6 DI.   (* Signal and power amplifiers入口 *)
    Let  j7 := joint  7 DO.   (* Signal and power amplifiers出口 *)
    Let  j8 := joint  8 DI.   (* Motor, load, and gears 入口 *)
    Let  j9 := joint  9 DO.   (* Motor, load, and gears 出口 *)
    Let j10 := joint 10 DI.   (* Ouput transducer入口 *)
    Let j11 := joint 11 DO.   (* Output transducer出口 *)
    Let j12 := joint 12 DI.   (* 出口处 *)
    
    (* 所有的方框 *)
    Let bIT := mkBlock "Input transducer" j1 j2.
    Let bAmp := mkBlock "Amplifier" j6 j7.
    Let bGear := mkBlock "Gear" j8 j9.
    Let bOT := mkBlock "Output transducer" j10 j11.
    
    (* 所有的汇合点 *)
    Let s0 := mkSumming [(j3,SPos);(j4,SNeg)] j5.
    
    (* 所有的连线 *)
    Let l0 := mkLine "Angular input" j0 j1.
    Let l1 := mkLine "Voltage proportional to input" j2 j3.
    Let l2 := mkLine "Error or Actuating signal" j5 j6.
    Let l3 := mkLine "" j7 j8.
    Let l4 := mkLine "Angular output" j9 j12.
    Let l5 := mkLine "" j9 j10.
    Let l6 := mkLine "Voltage proportional to output" j11 j4.
    
    (* 方框图 *)
    Let bd0 := mkBD "Antenna azimuth position control system"
      [bIT;bAmp;bGear;bOT] [s0] [l0;l1;l2;l3;l4;l5;l6] j0 j12.
    
    (* 对外的名称 *)
    Definition bdAPCS := bd0.
    
    (* 手动构造C2 *)
    Let c2_ex1 : C2 := (j0,j1).
    
    (* 自动找出所有C2 *)
    (* Compute bdC2_line bd0. *)
    (* Compute bdC2_blk bd0. *)
    (* Compute bdC2_sum bd0. *)
    
    
  End AntennaPositionControlSystem.
  
(*   Print bdAPCS. *)

End FunctionalBlockDiagram.
