(*
  Copyright 2024 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : base for differential equation
  author    : Zhengpu Shi
  date      : 2024.05

  ref       :
  * Wang Yi Peng's work
  * https://en.wikipedia.org/wiki/Linear_differential_equation#Second-order_case
  * 高等数学学习手册，徐小湛
  * https://www.math.ncue.edu.tw/~kwlee/ODEBoyce/DEChapter3.pdf
 *)


Require Export Calculus.
From FinMatrix Require Export Complex MyExtrOCamlR.

Open Scope C_scope.
Open Scope R_scope.
Open Scope RFun_scope.
