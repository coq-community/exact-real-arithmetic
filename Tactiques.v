Require Import definition.
Require Export ZArithRing.
Require Export RealField.

Ltac RingReplace x y := 
  change x with y || (replace x with y; [ idtac | ring ]).
