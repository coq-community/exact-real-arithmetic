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

Definition B_powerRZ (z : Z) : R := powerRZ (INR B) z.

Definition B_powerZ (z : Z) : Z := (Z_of_nat B ^ z)%Z.

Definition encadrement (xc : Reelc) (x : R) : Prop :=
  forall n : Z, (IZR (xc n) - 1 < x * B_powerRZ n < IZR (xc n) + 1)%R.

Definition encadrement_bis (p n : Z) (x : R) : Prop :=
  (IZR p - 1 < x * B_powerRZ n < IZR p + 1)%R.

Parameter gauss_z_sur_B : Z -> Z.

Parameter gauss_z_sur_B_pow : Z -> Z -> Z.

Parameter le_nat : R -> nat.

Definition oppose_reelc (xc : Reelc) : Reelc := fun n : Z => (- xc n)%Z.

Definition absolue_reelc (xc : Reelc) : Reelc := fun n : Z => Zabs (xc n).

Definition addition_reelc (xc yc : Reelc) : Reelc :=
  fun n : Z => gauss_z_sur_B (xc (n + 1)%Z + yc (n + 1)%Z).
 
Parameter msd : Reelc -> Z.

Definition p_max (xc : Reelc) (n : Z) : Z :=
  Zmax (n - msd xc + 3) (Zeven.Zdiv2 (n + 2)). 

Definition multiplication_reelc (xc yc : Reelc) : Reelc :=
  fun n : Z =>
  (Zsgn (xc (p_max yc n)) * Zsgn (yc (p_max xc n)) *
   gauss_z_sur_B_pow (1 + Zabs (xc (p_max yc n) * yc (p_max xc n)))
     (p_max yc n + p_max xc n - n))%Z.

Require Import Zdiv.

Definition Zdiv_sup (a b : Z) :=
  match Z_zerop (a mod b) with
  | left _ => (a / b)%Z
  | right _ => Zsucc (a / b)
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
  fun n : Z => Zsqrt (xc (Zsucc (Zsucc 0) * n)%Z).










