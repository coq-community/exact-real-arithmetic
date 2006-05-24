(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import Reals.

Parameter Rlog : R -> R -> R.

Axiom
  Rlog_powerRZ :
    forall r b : R,
    (0 < r)%R -> (1 < b)%R -> powerRZ b (Int_part (Rlog r b)) = r. 