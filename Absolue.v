(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition.
Require Import Tactiques.
Require Import Axiomes.
Require Import Lemmes.
Require Import sg.
Require Import Rbase_doubles_inegalites.

Lemma absolue_correct :
 forall (X : R) (XC : Reelc),
 encadrement XC X -> encadrement (absolue_reelc XC) (Rabs X). 

Proof.
intros.
unfold encadrement in |- *.
intro; unfold absolue_reelc in |- *.
generalize (H n).
cut ({(0 < XC n)%Z} + {0%Z = XC n} + {(0 > XC n)%Z}).
intro.
elim H0.
intro.
elim a.
intro.
replace (Z.abs (XC n)) with (XC n);
 [ rewrite <- Rabsolu_sg
 | symmetry  in |- *; apply Z.abs_eq; apply Zlt_le_weak; auto ].
replace (sg X) with 1%Z;
 [ simpl in |- *; rewrite Rmult_1_l; tauto
 | symmetry  in |- *; apply sg_pos; apply sg_Zsgn with XC n; [ auto | auto ] ]. 
clear H0 a.
intro.
rewrite <- b; simpl in |- *; RingReplace (0 - 1)%R (-1)%R;
 RingReplace (0 + 1)%R 1%R. 
cut ((0 < X)%R \/ 0%R = X \/ (0 > X)%R); [ intro | apply Rtotal_order ].
rewrite <- Rabsolu_sg.
elim H0.
intro; replace (sg X) with 1%Z;
 [ simpl in |- *; rewrite Rmult_1_l; tauto
 | symmetry  in |- *; apply sg_pos; auto ].
intro; elim H1.
intro; rewrite <- H2; replace (sg X) with 0%Z;
 [ simpl in |- *; rewrite Rmult_0_r; tauto
 | symmetry  in |- *; apply sg_nul; auto ].
intro; replace (sg X) with (-1)%Z;
  [ simpl | now symmetry; apply sg_neg; auto ].
replace  (-1 * X * B_powerRZ n)%R with  (- (X * B_powerRZ n))%R by ring.
intro.
pattern 1%R; RingReplace 1%R (- -1)%R; apply Rlt_2_Ropp_r; tauto.
intro.
replace (Z.abs (XC n)) with (- XC n)%Z;
 [ rewrite Ropp_Ropp_IZR ; rewrite <- Rabsolu_sg
 | symmetry  in |- *; apply Zabs_non_eq; apply Zlt_le_weak; apply Z.gt_lt;
   auto ].
replace (sg X) with (-1)%Z;
 [ simpl in |- *
 | symmetry  in |- *; apply sg_neg; apply sg_Zsgn_2 with XC n;
    [ auto | auto ] ].
intro; repeat rewrite Ropp_mult_distr_l_reverse.
RingReplace (- IZR (XC n) - 1)%R (- (IZR (XC n) + 1))%R;
 RingReplace (- IZR (XC n) + 1)%R (- (IZR (XC n) - 1))%R.
replace  (-1 * X * B_powerRZ n)%R with  (- (X * B_powerRZ n))%R by ring.
apply Rlt_2_Ropp_r; auto.
unfold Z.lt in |- *; unfold Z.gt in |- *.
apply Zcompare_rec with (n := 0%Z) (m := XC n).
intro; left; right.
generalize (Zcompare_Eq_iff_eq 0 (XC n)).
intro.
elim H1.
auto with arith.
intro; left; left; auto.
intro; right; auto.
Qed.

Hint Resolve absolue_correct: real.
