Require Import definition.

Ltac RingReplace x y := replace x with y; [ idtac | ring ].