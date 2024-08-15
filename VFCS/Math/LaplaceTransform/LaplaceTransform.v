(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : Laplace transform 的一些扩展
  author      : Zhengpu Shi
  date        : 2022.08
  
  ref         :
  1. Control Systems Engineering by Norman S. Nise
  
  remark      :
  1. 在控制系统中，常使用拉氏变换 L 和逆拉式变换 L' 对时域的微分方程和
    频域的复变量代数方程进行相互转换。
    对一个复杂函数进行 L'，我们可以将该函数转换为简单项的和，这些简单项的 L' 可查表获得。
    该转换过程(结果)称为 partial-fraction expansion (分式展开).
    
    形如 F(s)=N(s)/D(s) 的复函数，当 N(s) 的阶小于 D(s) 的阶时，PFE可以进行，
    当 N(S) 的阶 >= D(s) 的阶时，N(s) 必须用 D(s) 依次相除直到这个余式的分子比分母
    的阶小。
  
    例如：
            s^3 + 2 s^2 + 6 s + 7                        2
    F(s) = -------------------------     = s + 1 + -------------，记余式为 F1(s)
                s^2 + s + 5                         s^2 + s + 5
    
    下一步，是对余式 F1(s) 进行分式展开。
    首先对分母上的多项式 s^2+s+5 进行因式分解，
    然后利用待定系数法或留数法算出待定系数。
  
  2. 形式化要研究的问题
    (1) 有理式的定义和运算。有理式包括：整式，分式。整式包含：多项式，单项式。
    (2) 假分式化成真分式；
    (3) 复数域中的一元多项式因式分解；
    (4) 待定系数法；
    (5) 留数法
*)


(* ######################################################################### *)
(** * 有理分式展开 *)
