(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export ZArith.
Require Export Zcomplements.
Require Export Reals.
Require Export Omega.
Require Export Arith.
Require Export ZArith.
Require Export Zmisc.
Require Export Zpower. 
Require Export Zmax.

Definition Reelc := Z -> Z.

Parameter B : nat.

Definition nearest_Int (x : R) : Z := up (x - / 2).

Definition gauss_z_sur_B (x : Z) := nearest_Int (IZR x / INR B).

Definition B_powerRZ (z : Z) : R := powerRZ (INR B) z.

Definition gauss_z_sur_B_pow x n := nearest_Int (IZR x / B_powerRZ n).

Lemma nearest_Int_correct (x : R) :
  (x - / 2 < IZR (nearest_Int x) <= x + / 2)%R.
Proof.
unfold nearest_Int.
destruct (archimed (x - / 2)) as [above below].
split;[now apply above | ].
apply (Rplus_le_reg_r (- (x - / 2))).
replace (x + (/ 2) + - (x - /2))%R with 1%R by field.
now apply below.
Qed.

Lemma gauss_correct :
   forall z : Z,
    (IZR z * / INR B - 1 * / 2 < IZR (gauss_z_sur_B z) <=
     IZR z * / INR B + 1 * / 2)%R.
Proof.
intros z.
rewrite !Rmult_1_l.
now apply nearest_Int_correct.
Qed.

Lemma gauss_correct_pow :
    forall z n : Z,
    (IZR z * / B_powerRZ n - 1 * / 2 < IZR (gauss_z_sur_B_pow z n) <=
     IZR z * / B_powerRZ n + 1 * / 2)%R.
Proof.
intros z n.
rewrite !Rmult_1_l.
apply nearest_Int_correct.
Qed.

Definition B_powerZ (z : Z) : Z := (Z_of_nat B ^ z)%Z.

Definition encadrement (xc : Reelc) (x : R) : Prop :=
  forall n : Z, (IZR (xc n) - 1 < x * B_powerRZ n < IZR (xc n) + 1)%R.

Definition encadrement_bis (p n : Z) (x : R) : Prop :=
  (IZR p - 1 < x * B_powerRZ n < IZR p + 1)%R.

Parameter le_nat : R -> nat.

Definition oppose_reelc (xc : Reelc) : Reelc := fun n : Z => (- xc n)%Z.

Definition absolue_reelc (xc : Reelc) : Reelc := fun n : Z => Z.abs (xc n).

Definition addition_reelc (xc yc : Reelc) : Reelc :=
  fun n : Z => gauss_z_sur_B (xc (n + 1)%Z + yc (n + 1)%Z).
 
Parameter msd : Reelc -> Z.

Definition p_max (xc : Reelc) (n : Z) : Z :=
  Zmax (n - msd xc + 3) (Z.quot2 (n + 2)). 

Definition multiplication_reelc (xc yc : Reelc) : Reelc :=
  fun n : Z =>
  (Z.sgn (xc (p_max yc n)) * Z.sgn (yc (p_max xc n)) *
   gauss_z_sur_B_pow (1 + Z.abs (xc (p_max yc n) * yc (p_max xc n)))
     (p_max yc n + p_max xc n - n))%Z.

Require Import Zdiv.

Definition Zdiv_sup (a b : Z) :=
  match Z_zerop (a mod b) with
  | left _ => (a / b)%Z
  | right _ => Z.succ (a / b)
  end.

Definition inverse_reelc (xc : Reelc) : Reelc :=
  fun n : Z =>
  match Z_le_gt_dec n (- msd xc) with
  | left _ => 0%Z
  | right _ =>
      match Z_gt_le_dec (xc (n + 2 * msd xc + 1)%Z) 1 with
      | left _ =>
          Zdiv_sup (B_powerZ (2 * n + 2 * msd xc + 1))
            (xc (n + 2 * msd xc + 1)%Z)
      | right _ =>
          (B_powerZ (2 * n + 2 * msd xc + 1) / xc (n + 2 * msd xc + 1))%Z
      end
  end.    

Definition racine_reelc (xc : Reelc) : Reelc :=
  fun n : Z => Z.sqrt (xc (Z.succ (Z.succ 0) * n)%Z).










