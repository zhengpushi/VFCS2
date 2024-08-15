Require Import Reals.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Open Scope R_scope.


Parameters c w : R.
Variable t :R.
Variables f : R-> R.
Variable b l: Rbar.

(*
Definition exp1 (t:R) : R :=
exp (-c * t).

Definition cos1 (t:R) : R :=
cos (w * t).

Definition sin1 (t:R) : R :=
sin (w * t).

Definition exp1 : R->R := fun t => exp (-c * t).
Definition cos1 : R->R := fun t => cos (w * t).
Definition sin1 : R->R := fun t => sin (w * t).

Definition ref : R->R := f *f exp1 *f cos1.
Definition imf : R->R := fopp f *f exp1 *f sin1.


Definition ref (t:R) : R :=
f t * exp1 t * cos1 t.

Definition imf (t:R) : R :=
- (f t) * exp1 t * sin1 t.
*)

Definition ref (t:R) : R :=
 f t * exp (-c * t) * cos (w * t).

Definition imf (t:R) : R :=
- f t * exp (-c * t) * sin (w * t).


Definition lap1 := RInt ref 0 b.
Definition lap2 := RInt imf 0 b.

Definition Rtof (t:R) :R :=
RInt ref 0 t.











