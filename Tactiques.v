Require Import definition.
Require Export LegacyZArithRing.
Require Export LegacyRfield.

Ltac RingReplace x y := 
  change x with y || (replace x with y; [ idtac | legacy ring ]).
