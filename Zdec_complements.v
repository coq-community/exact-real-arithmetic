Require Import ZArith.


Lemma Zabs_Zle_1 : forall z : Z, {Zabs z = 0%Z} + {(0 < Zabs z)%Z}.

Proof.
intros.
destruct z.
auto with arith.
right.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.
right.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.
Qed.

Hint Resolve Zabs_Zle_1: real.



Lemma Zabs_Zle_2 :
 forall z z1 : Z, {z = 0%Z /\ z1 = 0%Z} + {(0 < Zabs z)%Z \/ (0 < Zabs z1)%Z}.

Proof.
intros.
destruct z.
destruct z1.
left.
auto with arith.
right; right.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.
do 2 right.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.
right.
left.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.
right.
left.
simpl in |- *.
apply Zgt_lt.
apply Zorder.Zgt_pos_0.

Qed.

Hint Resolve Zabs_Zle_2: real.


Lemma Zlt_le_ind : forall z z1 : Z, (z1 <= z)%Z \/ (z <= z1)%Z.

Proof.
intros.
cut ({(z1 <= z)%Z} + {(z1 > z)%Z}); [ intro | apply Z_le_gt_dec ].
elim H.
intro.
left; auto.
intro; right; apply Zlt_le_weak; apply Zgt_lt; auto.
Qed.


