Require Import ZArith.
Require Import Reals.

Lemma Zpower_le_0 : forall z z1 : Z, (0 < z)%Z -> (0 <= z ^ z1)%Z.

Proof.
intros.
unfold Zpower in |- *.
case z1.
omega.
intro.
rewrite Zpower_pos_nat.
apply Zpower_NR0.
auto with zarith.
intro; omega.
Qed.


Hint Resolve Zpower_le_0: zarith.