Require Import Reals.

Parameter Rlog : R -> R -> R.

Axiom
  Rlog_powerRZ :
    forall r b : R,
    (0 < r)%R -> (1 < b)%R -> powerRZ b (Int_part (Rlog r b)) = r. 