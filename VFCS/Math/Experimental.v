(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Experimental formal mathematical theory.
  author    : Zhengpu Shi
  date      : 2023.04

 *)


(**
   《普林斯顿数学指南》I.3 基本数学定义， Q[x]/(x^3 - x - 1) 构成了域，
   这是与不可约多项式问题，以及用在AES加密算法中的处理有关。
   既然是域，而且Coq有域的自动求解能力，但是已构建的算法的证明又非常繁琐（需十几个小时）
   那么，能否利用field策略来自动完成？有没有可能？
   具体定义运算时，可参考在Q中处理Qeq时的做法。
   
   这是一个商群的问题，还涉及到子群，左陪集，共轭元，正规子群等概念。

   需要进一步检查这个想法，也许是一个单独的课题
 *)


   

