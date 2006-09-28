Require Import definition.
Require Export LegacyZArithRing.

Ltac RingReplace x y := 
  change x with y || (replace x with y; [ idtac | legacy ring ]).
