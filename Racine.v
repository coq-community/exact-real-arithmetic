(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Import definition.
Require Import Reals.
Require Import Zind_complements.
Require Import Tactiques.
Require Import Psatz.
Require Import Lemmes.
Require Import Zsqrt_complements.
Require Import Rbase_inegalites.
Require Import Lemmes_generaux.
Require Import Rbase_doubles_inegalites.
Require Import Zarith_inegalites.
Require Import Zarith_operations.
Require Import powerRZ_complements.
Require Import Inverse.

Lemma contraposesg_Zsgn_2 :
 forall (x : R) (xc : Reelc) (n : Z),
 encadrement xc x -> x >= 0 ->  ( xc n >= 0)%Z .
Proof.
intros x xc n H.
assert (implique : forall A B : Prop, (~A -> ~B) -> (B -> A)).
intros A B H2. apply Classical_Prop.or_to_imply.
apply Classical_Prop.imply_to_or in H2.
apply or_comm. apply Classical_Prop.imply_and_or2 with (~~A).
apply Classical_Prop.NNPP. assumption.
apply implique. assert (implique2 :  (x < 0) -> (~ x >= 0)).
apply Classical_Prop.or_to_imply.
apply Classical_Prop.imply_and_or2 with (x >= 0).
intros H2. apply RIneq.Rle_not_lt. apply Rge_le.
assumption. apply Classical_Prop.classic.
intros H8. apply implique2.
 assert (implique3 : (~ (xc n >= 0)%Z) -> ((xc n < 0)%Z)).
apply Znot_ge_lt.
apply sg_Zsgn_2 with xc n. assumption.
apply Z.lt_gt. apply implique3. assumption.
Qed.

Lemma geqZ : forall z : Z,
(z >= 0)%Z -> ((0=z)%Z)\/((0 < z)%Z).
Proof.
intros z H. apply Z.ge_le in H.
apply Zle_lt_or_eq in H.
apply or_comm in H.
assumption.
Qed.

Lemma existcarre : forall z : Z,
(exists z2 : Z, (z2*z2 = z)%Z)\/(forall z2 : Z, (z2* z2 <> z)%Z).
Proof.
intros z.
assert (H :(~(forall z2 : Z, (z2* z2 <> z)%Z)) ->
           (exists z2 : Z, (z2*z2 = z)%Z)).
intros H. apply Classical_Pred_Type.not_all_ex_not in H.
inversion H. assert ((~ (x * x)%Z <> z) -> (x * x)%Z = z).
intros H2. apply Z.eq_dne. assumption.
assert (H2 : (x * x)%Z = z).  apply H1.
assumption.
  apply ex_intro with (x). assumption.
apply Classical_Prop.imply_and_or2 with (~ (forall z2 : Z, (z2 * z2)%Z <> z)).
assumption. apply or_comm. apply Classical_Prop.classic.
Qed.

Lemma racineineq : forall a b : R,
a >= 0 -> b >= 0 -> a * a >= b * b -> a >= b.
Proof. intros a b H1 H2 H3.
replace (a) with (sqrt (a * a)).
replace (b) with (sqrt (b * b)).
apply Rle_ge. apply sqrt_le_1_alt. apply Rge_le. assumption.
rewrite sqrt_square. reflexivity. apply Rge_le. assumption.
rewrite sqrt_square. reflexivity. apply Rge_le. assumption.
Qed.

Lemma plusracine : forall r : R,
r >= 0 -> sqrt r >= sqrt(r + 1) - 1.
Proof. intros r H.
replace (sqrt (r + 1) - 1) with (sqrt (r + 1) + (- 1)).
replace (sqrt r) with (sqrt r + 1 + (-1)).
apply Rplus_ge_compat_r. apply racineineq.
apply Rge_trans with (1). replace (1) with (0 + 1).
replace (sqrt r + (0 + 1)) with (sqrt r + 1).
apply Rplus_ge_compat_r. apply Rle_ge. apply sqrt_positivity.
apply Rge_le. assumption. ring. ring. lra.
apply Rle_ge. apply sqrt_positivity. apply Rge_le.
apply Rge_trans with (1). replace (1) with (0 + 1).
replace (r + (0 + 1)) with (r + 1).
apply Rplus_ge_compat_r. assumption. ring. ring. lra.
rewrite sqrt_sqrt. replace ((sqrt r + 1) * (sqrt r + 1)) with
(sqrt r * sqrt r + 1 * 1 + sqrt r + sqrt r). rewrite sqrt_sqrt.
replace (r + 1 * 1 + sqrt r + sqrt r) with (r + (1 * 1 + sqrt r + sqrt r)).
apply Rplus_ge_compat_l. replace (1 * 1) with (1).
replace (1) with (1 + 0). replace (1 + 0 + sqrt r + sqrt r) with
(1  + 2* sqrt r). apply Rplus_ge_compat_l. replace (0) with (2 * 0).
apply Rmult_ge_compat_l. lra. apply Rle_ge. apply sqrt_positivity.
apply Rge_le. assumption. ring. ring. ring. ring. ring.
apply Rge_le. assumption. ring. apply Rge_le.
apply Rge_trans with (1). replace (1) with (0 + 1).
replace (r + (0 + 1)) with (r + 1).
apply Rplus_ge_compat_r. assumption. ring. ring. lra.
ring. ring.
Qed.

Lemma sqrtB2n : forall z : Z,
sqrt (B_powerRZ (2 * z)) = B_powerRZ z.
Proof. intros z. replace (B_powerRZ (2 * z)) with
(B_powerRZ (z) * B_powerRZ (z)).
apply sqrt_square. apply Rlt_le. apply Rgt_lt.
apply Bexpos. rewrite produitB_powerRZ. unfold B_powerRZ.
apply powerRZ_trivial. ring. Qed.

Lemma zetzplusunnoncarre : forall z : Z,
(z >= 0)%Z -> (forall z2 : Z, (z2* z2 <> z)%Z) -> (forall z2 : Z, (z2* z2 <> (z + 1)%Z)%Z) ->
(Z.sqrt z = Z.sqrt (z + 1))%Z.
Proof.
intros z H H1 H2.
assert (H3 : Z.sqrt (Z.succ z) = Z.succ (Z.sqrt z) \/
             Z.sqrt (Z.succ z) = Z.sqrt z).
apply Z.sqrt_succ_or. apply Z.ge_le. assumption.
replace (Z.succ z) with ((z + 1)%Z) in H3. inversion H3.
apply Z.sqrt_eq_succ_iff_square in H0. inversion H0. inversion H4.
replace (Z.succ z) with ((z + 1)%Z) in H6.
rewrite H6 in H2. assert (H7 : (x * x)%Z <> (x * x)%Z).
apply H2. replace ((x * x)%Z <> (x * x)%Z) with (False) in H7.
inversion H7. unfold not. omega. ring. apply Z.ge_le.
assumption. rewrite H0. reflexivity. ring.
Qed.

Lemma sqrtZ : forall z : Z,
(z > 0)%Z -> (Z.sqrt (z * z - 1) = z - 1)%Z.
Proof. intros z H.
replace ((z - 1)%Z) with (Z.pred (z)). rewrite <- Z.sqrt_pred_square.
replace ((z * z - 1)%Z) with (Z.pred(z * z)).
reflexivity. unfold Z.pred. ring. apply Z.gt_lt. assumption.
unfold Z.pred. ring. Qed.

Lemma plusracineZ : forall z : Z,
(z >= 0)%Z -> sqrt (IZR z + 1) <= IZR (Z.sqrt z) + 1.
Proof. intros z H.
assert (H1 : sqrt (IZR (z + 1%Z)) < IZR (Z.sqrt (z + 1%Z)) + 1).
apply Zsqrt_sqrt_bis. apply le_IZR.
apply Rle_trans with (1).
lra. replace (1) with (0 + 1). rewrite plus_IZR.
apply Rplus_le_compat_r. apply IZR_le. apply Z.ge_le.
assumption. ring.
rewrite plus_IZR in H1.
assert (H2 : (exists z2 : Z, (z2*z2 = z)%Z)\/(forall z2 : Z, (z2* z2 <> z)%Z)).
apply existcarre. inversion H2.
inversion H0. inversion H3. clear H3.
assert (K : (x >=0)%Z \/ (x<=0)%Z).
apply Classical_Prop.imply_and_or2 with ((0 <= x)%Z).
intros H5. apply Z.le_ge. assumption.
apply Z.le_ge_cases.
 inversion K.
rewrite Z.sqrt_square.
replace (IZR x) with (sqrt (IZR (x * x))).
replace (sqrt (IZR (x * x) + 1)) with (sqrt (IZR (x * x) + 1) - 1 + 1).
apply Rplus_le_compat_r. apply Rge_le.
apply plusracine. rewrite mult_IZR. replace (0) with
(0 * IZR x). apply Rmult_ge_compat_r. apply Rle_ge. apply IZR_le.
apply Z.ge_le. assumption.
apply Rle_ge. apply IZR_le. apply Z.ge_le. assumption.
ring. ring. rewrite mult_IZR. rewrite sqrt_square.
reflexivity. apply IZR_le. apply Z.ge_le. assumption.
apply Z.ge_le. assumption.
assert (K2 : ((-x) * (-x)= z)%Z).
replace ((- x * - x)%Z) with ((x * x)%Z).
assumption. ring.
assert (K3 : ((-x) >= 0)%Z).
apply Z.le_ge. apply le_IZR.
replace (0) with (0 + IZR (x) + (- IZR (x))). replace (IZR (- x)) with
(0 + (-IZR ( x))). apply Rplus_le_compat_r.
replace (0 + IZR x) with ( IZR x). apply IZR_le. assumption.
ring. replace (0 + - IZR x) with (0 - IZR x). rewrite <- minus_IZR.
apply IZR_trivial. ring. ring. ring.
assert (K4 : (x * x)%Z = (-x * -x)%Z). ring.
rewrite K4.
rewrite Z.sqrt_square.
replace (IZR (-x)) with (sqrt (IZR (-x * -x))).
replace (sqrt (IZR (-x * -x) + 1)) with (sqrt (IZR (-x * -x) + 1) - 1 + 1).
apply Rplus_le_compat_r. apply Rge_le.
apply plusracine. rewrite mult_IZR. replace (0) with
(0 * IZR (-x)). apply Rmult_ge_compat_r. apply Rle_ge. apply IZR_le.
apply Z.ge_le. assumption.
apply Rle_ge. apply IZR_le. apply Z.ge_le. assumption.
ring. ring. rewrite mult_IZR. rewrite sqrt_square.
reflexivity. apply IZR_le. apply Z.ge_le. assumption.
apply Z.ge_le. assumption.
assert (H3 : (exists z2 : Z, (z2 * z2)%Z = (z + 1)%Z) \/
(forall z2 : Z, (z2 * z2)%Z <> (z + 1)%Z)).
apply existcarre. inversion H3. inversion H4. inversion H5.
assert (K : (x >=0)%Z \/ (x<=0)%Z).
apply Classical_Prop.imply_and_or2 with ((0 <= x)%Z).
intros H6. apply Z.le_ge. assumption.
apply Z.le_ge_cases. inversion K.

assert (M : ((0=x)%Z)\/((0 < x)%Z)). apply geqZ. assumption.
inversion M. rewrite <- H8 in H7.
rewrite <- plus_IZR. rewrite <- H7.
replace (IZR (0 * 0)) with (0). apply Rle_trans with (IZR (Z.sqrt z)).
rewrite sqrt_0. apply IZR_le. apply Zsqrt_pos.
replace (IZR (Z.sqrt z)) with (IZR (Z.sqrt z) + 0).
replace (IZR (Z.sqrt z) + 0 + 1) with (IZR (Z.sqrt z) + 1).
apply Rplus_le_compat_l. lra. ring. ring. rewrite mult_IZR.
ring. clear H5. rewrite <- plus_IZR. rewrite <- H7. rewrite mult_IZR.
rewrite sqrt_square. assert (H9 : (x * x - 1)%Z = z%Z).
apply eq_IZR. rewrite minus_IZR.
replace (IZR (x * x) - 1) with (IZR (x * x) + (- 1)).
replace (IZR z) with (IZR z + 1 + (-1)).
apply Rplus_eq_compat_r. rewrite <- plus_IZR. apply IZR_trivial.
assumption. ring. ring.
rewrite <- H9. rewrite sqrtZ. rewrite minus_IZR.
replace (IZR x - 1 + 1) with (IZR x). lra.
ring. apply Z.lt_gt. assumption. apply IZR_le. apply Z.ge_le.
apply Z.le_ge. apply le_IZR.
apply Rlt_le. apply IZR_lt. assumption.

assert (M : ((0=x)%Z)\/((0 > x)%Z)).
apply Classical_Prop.imply_and_or2 with ((x = 0)%Z).
intros H8. symmetry in H8. assumption. apply or_comm.
apply Classical_Prop.imply_and_or2 with ((x < 0)%Z).
intros H8. apply Z.lt_gt. assumption.
apply  Zle_lt_or_eq. assumption.
inversion M. rewrite <- H8 in H7.
rewrite <- plus_IZR. rewrite <- H7.
replace (IZR (0 * 0)) with (0). apply Rle_trans with (IZR (Z.sqrt z)).
rewrite sqrt_0. apply IZR_le. apply Zsqrt_pos.
replace (IZR (Z.sqrt z)) with (IZR (Z.sqrt z) + 0).
replace (IZR (Z.sqrt z) + 0 + 1) with (IZR (Z.sqrt z) + 1).
apply Rplus_le_compat_l. lra. ring. ring. rewrite mult_IZR.
ring. clear H5. rewrite <- plus_IZR. rewrite <- H7. rewrite mult_IZR.
replace (IZR x * IZR x) with (IZR (-x) * IZR (-x)).
rewrite sqrt_square. assert (H9 : (-x * -x - 1)%Z = z%Z).
apply eq_IZR. rewrite minus_IZR. replace (IZR (- x * - x))
with (IZR ( x *  x)).
replace (IZR (x * x) - 1) with (IZR (x * x) + (- 1)).
replace (IZR z) with (IZR z + 1 + (-1)).
apply Rplus_eq_compat_r. rewrite <- plus_IZR. apply IZR_trivial.
assumption. ring. ring.
apply IZR_trivial. ring.
rewrite <- H9. rewrite sqrtZ. rewrite minus_IZR.
replace (IZR (-x) - 1 + 1) with (IZR (-x)). lra.
ring. replace ((-x)%Z) with ((0 + (-x))%Z).
apply Z.lt_gt. apply lt_IZR. replace (0) with (IZR x + IZR(-x)).
rewrite plus_IZR. apply Rplus_lt_compat_r. apply IZR_lt.
apply Z.gt_lt. assumption. rewrite <- plus_IZR. apply IZR_trivial. ring. ring.
replace (IZR (- x)) with (IZR (0 + (-x))).
replace (0) with (IZR x + IZR (-x)). rewrite plus_IZR.
apply Rplus_le_compat_r. apply IZR_le. assumption.
rewrite <- plus_IZR. apply IZR_trivial. ring.
rewrite plus_IZR. ring. rewrite <- !mult_IZR. apply f_equal.
ring.
assert (H8 : (Z.sqrt z = Z.sqrt (z + 1))%Z).
apply zetzplusunnoncarre. assumption.
 assumption.  assumption.
rewrite H8. apply Rlt_le. assumption.
Qed.

Lemma racine_correct :
 forall (x : R) (xc : Reelc),
 0 <= x -> encadrement xc x -> encadrement (racine_reelc xc) (sqrt x).

Proof.
intros x xc H0. intro H.
unfold encadrement. intros n.
assert (H2 : (xc (2*n) >= 0)%Z). apply contraposesg_Zsgn_2 with x.
assumption. apply Rle_ge. assumption.
assert (H3 : ((0=xc (2*n))%Z)\/((0 <xc (2*n))%Z)).
apply geqZ.  assumption. inversion H3.
unfold racine_reelc. replace (Z.succ (Z.succ 0)) with (2%Z).
rewrite <- H1. rewrite Zsqrt_0. replace (0 - 1) with (-1).
replace (0 + 1) with (1).
unfold encadrement in H.
assert (H4 : IZR (xc (2*n)%Z) - 1 < x * B_powerRZ ((2*n)%Z) < IZR (xc (2*n)%Z) + 1).
apply H. rewrite <- H1 in H4. replace (0 - 1) with (-1) in H4.
replace (0 + 1) with (1) in H4.
split. apply Rlt_le_trans with (0). lra.
replace (0) with (0 * 0). apply Rmult_le_compat. lra.
lra. apply sqrt_pos. apply Rlt_le. apply Rgt_lt.
apply Bexpos. ring.
inversion H4. clear H4. clear H5. apply Rgt_lt.
assert (H7 : x < 1 * / B_powerRZ (2 * n)).
replace (x) with (x * B_powerRZ (2 * n) * / B_powerRZ (2 * n)).
apply Rmult_lt_compat_r. apply Rinv_0_lt_compat. apply Rgt_lt.
apply Bexpos. assumption. rewrite Rinv_r_simpl_l. reflexivity.
apply Rgt_not_eq. apply Bexpos.
replace (1 * / B_powerRZ (2 * n)) with (B_powerRZ (-2 * n)) in H7.
replace (1) with (/ B_powerRZ n * B_powerRZ n).
apply Rmult_gt_compat_r. apply Bexpos.
replace (/ B_powerRZ n) with (B_powerRZ (-n)). apply Rlt_gt.
replace (B_powerRZ (- n)) with (sqrt (B_powerRZ (-2 * n))).
apply sqrt_lt_1_alt. split. assumption. assumption.
replace ((-2 * n)%Z) with ((2 * (-n))%Z).
rewrite sqrtB2n. reflexivity. ring.
 unfold B_powerRZ. rewrite Rinv_powerRZ.
reflexivity. apply Bneq0.  rewrite Rmult_comm.
replace (B_powerRZ n * / B_powerRZ n) with
(1 * B_powerRZ n * / B_powerRZ n). rewrite Rinv_r_simpl_l.
reflexivity. apply Rgt_not_eq. apply Bexpos. ring.
unfold B_powerRZ.  rewrite Rinv_powerRZ. replace
(1 * powerRZ (INR B) (- (2 * n))) with (powerRZ (INR B) (- (2 * n))).
apply powerRZ_trivial. ring. ring. apply Bneq0. ring. ring.
ring. ring. ring.

 - unfold encadrement in H.
assert (H4 : IZR (xc (2*n)%Z) - 1 < x * B_powerRZ (2*n) < IZR (xc (2*n)%Z) + 1).
apply H. unfold racine_reelc.  replace ((Z.succ (Z.succ 0))) with (2%Z).
inversion H4. split.
assert (H7 : IZR (xc (2 * n)%Z) < x * B_powerRZ (2 * n) + 1).
replace (IZR (xc (2 * n)%Z)) with (IZR (xc (2 * n)%Z) - 1 + 1).
apply Rplus_lt_compat_r. assumption. ring.
assert (H8 : sqrt (IZR (xc (2 * n)%Z)) < sqrt(x * B_powerRZ (2 * n) + 1)).
apply sqrt_lt_1_alt. split. apply Rlt_le.
apply IZR_lt. apply Z.gt_lt. apply Z.lt_gt. assumption. assumption.
assert (H9 : sqrt (IZR (xc (2 * n)%Z)) + (-1) < sqrt (x * B_powerRZ (2 * n) + 1) + (-1)).
apply Rplus_lt_compat_r. assumption.
replace (sqrt (IZR (xc (2 * n)%Z)) + -1) with (sqrt (IZR (xc (2 * n)%Z)) -1) in H9.
replace (sqrt (x * B_powerRZ (2 * n) + 1) + -1) with
 (sqrt (x * B_powerRZ (2 * n) + 1) -1) in H9.
apply Rle_lt_trans with (sqrt (IZR (xc (2 * n)%Z)) - 1).
replace (IZR (Z.sqrt (xc (2 * n)%Z)) - 1) with (IZR (Z.sqrt (xc (2 * n)%Z)) + (- 1)).
replace (sqrt (IZR (xc (2 * n)%Z)) - 1) with (sqrt (IZR (xc (2 * n)%Z)) + (- 1)).
apply Rplus_le_compat_r. apply Zsqrt_sqrt. apply le_IZR. apply Rlt_le.
apply IZR_lt. apply Z.gt_lt. apply Z.lt_gt. assumption. ring. ring.
apply Rlt_le_trans with (sqrt (x * B_powerRZ (2 * n) + 1) - 1).
replace (sqrt x * B_powerRZ n) with (sqrt (x * B_powerRZ (2 * n))).
assumption. rewrite sqrt_mult_alt. rewrite sqrtB2n. reflexivity.
assumption. replace (sqrt x * B_powerRZ n) with (sqrt (x * B_powerRZ (2 * n))).
apply Rge_le. apply plusracine.
replace (0) with (0 * B_powerRZ (2 * n)). apply Rmult_ge_compat_r.
apply Rgt_ge. apply Bexpos. apply Rle_ge. assumption.
ring. rewrite sqrt_mult_alt. rewrite sqrtB2n. reflexivity. assumption.
ring. ring.
assert (H7 : sqrt (x * B_powerRZ (2 * n)) < sqrt (IZR (xc (2 * n)%Z) + 1)).
apply sqrt_lt_1_alt. split. replace (0) with (0 * B_powerRZ (2 * n)).
apply Rmult_le_compat_r. apply Rlt_le. apply Rgt_lt. apply Bexpos.
assumption. ring. assumption.
replace (sqrt (x * B_powerRZ (2 * n))) with (sqrt x * B_powerRZ n) in H7.
apply Rlt_le_trans with (sqrt (IZR (xc (2 * n)%Z) + 1)).
assumption. apply plusracineZ. assumption.
rewrite sqrt_mult_alt. rewrite sqrtB2n. reflexivity. assumption. ring.
Qed.
