(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition. 
Require Import Tactiques.
Require Import Rbase_doubles_inegalites.

Axiom B_sup_4 : 4 <= B.

Axiom msd_c :
    forall xc : Reelc,
    (forall n : Z, (n < msd xc)%Z -> (Z.abs (xc n) <= 1)%Z) /\
    (Z.abs (xc (msd xc)) > 1)%Z. 

Lemma inconsistent_msd: False.
Proof.
destruct (msd_c (fun x => 0%Z)) as [_ it].
revert it; discriminate.
Qed.

Lemma intermediaire :
 forall (xc : Reelc) (m : Z),
 msd xc = m ->
 (forall n : Z, (n < m)%Z -> (Z.abs (xc n) <= 1)%Z) /\ (Z.abs (xc m) > 1)%Z.
Proof.                  
intros xc m a.
rewrite <- a.
apply msd_c.
Qed.

Lemma msd_c_bis :
 forall (xc : Reelc) (m : Z),
 (forall n : Z, (n < m)%Z -> (Z.abs (xc n) <= 1)%Z) /\ (Z.abs (xc m) > 1)%Z ->
 msd xc = m. 
Proof.
intros xc m (H1, H2).
generalize (msd_c xc); intuition.
assert (cmp : (m < msd xc)%Z \/ m = msd xc \/ (msd xc < m)%Z).
omega.
intuition.
generalize (H0 m H); intro; omega.
generalize (H1 (msd xc) H4); intro; omega.
Qed.

Lemma msd_c_ter : forall xc : Reelc, (1 < Z.abs (xc (msd xc)))%Z.
Proof.
intros.
apply Z.gt_lt.
generalize (msd_c xc); intros (h1, h2).
generalize (h1 (Z.pred (msd xc))); auto.
Qed.


Lemma msd_c_4 : forall xc : Reelc, (IZR (Z.abs (xc (Z.pred (msd xc)))) <= 1)%R.
Proof.
intros.
RingReplace 1%R (IZR (Z.succ 0)); apply IZR_le.
simpl in |- *.
generalize (msd_c xc); intros (h1, h2).
generalize (h1 (Z.pred (msd xc))); intro.
auto with zarith.
Qed.


Lemma xc_nul :
 forall (x : R) (xc : Reelc) (n : Z),
 x = 0%R -> encadrement xc x -> xc n = 0%Z.
Proof.
intros.
generalize (H0 n); clear H0.
rewrite H.
RingReplace (0 * B_powerRZ n)%R 0%R.
intro.
apply one_IZR_lt1.
apply Rlt_2_minus_r with (IZR (xc n)).
RingReplace (-1 - IZR (xc n))%R (- (IZR (xc n) + 1))%R.
RingReplace (1 - IZR (xc n))%R (- (IZR (xc n) - 1))%R.
RingReplace (IZR (xc n) - IZR (xc n))%R (-0)%R.
apply Rlt_2_Ropp_r.
auto.
Qed.