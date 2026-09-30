import Mathlib
import LowerCertificateSoundness

namespace LittlewoodCylinders.LowerCertificate

open scoped BigOperators Matrix
open LowerCertificateData

abbrev preconditionerR : Matrix I I ℝ := fun i j => (preconditioner i j : ℝ)
abbrev jacobianR : Matrix I I ℝ := fun i j => (jacobian i j : ℝ)

abbrev errorEntryQ (i j : I) : ℚ :=
  (if i = j then 1 else 0) - ∑ k : I, preconditioner i k * jacobian k j

abbrev errorEntryR (i j : I) : ℝ := (errorEntryQ i j : ℝ)

lemma errorEntryR_eq (i j : I) :
    errorEntryR i j = (if i = j then 1 else 0) - ∑ k : I,
      preconditionerR i k * jacobianR k j := by
  simp only [errorEntryR, errorEntryQ, preconditionerR, jacobianR]
  push_cast
  by_cases h : i = j <;> simp [h]

lemma inverseErrorTotal_nonneg : 0 ≤ inverseErrorTotal := by
  rw [inverseErrorTotal]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

lemma error_row_le_total (i : I) :
    ∑ j : I, |errorEntryQ i j| ≤ inverseErrorTotal := by
  rw [inverseErrorTotal]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun k : I => ∑ j : I, |errorEntryQ k j|)
    (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

lemma inverseErrorTotal_eq_certified :
    inverseErrorTotal = certifiedInverseErrorTotal := by
  rfl

lemma inverseErrorTotal_lt_half : inverseErrorTotal < 1 / 2 := by
  rw [inverseErrorTotal_eq_certified]
  exact certificate_preconditioner

lemma sub_mulVec_mulVec_coord (x : V) (i : I) :
    (x - preconditionerR *ᵥ (jacobianR *ᵥ x)) i =
      ∑ j : I, errorEntryR i j * x j := by
  rw [Pi.sub_apply]
  simp only [Matrix.mulVec, dotProduct, errorEntryR_eq]
  simp only [preconditionerR, jacobianR]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul]
  rw [show (∑ j : I, if i = j then x j else 0) = x i by simp]
  rw [Finset.sum_comm]
  apply sub_right_inj.mpr
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sub_mulVec_mulVec_norm_le (x : V) :
    ‖x - preconditionerR *ᵥ (jacobianR *ᵥ x)‖ ≤
      (inverseErrorTotal : ℝ) * ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Rat.cast_nonneg.mpr inverseErrorTotal_nonneg)
    (norm_nonneg _))]
  intro i
  rw [sub_mulVec_mulVec_coord]
  calc
    ‖∑ j : I, errorEntryR i j * x j‖ ≤
        ∑ j : I, ‖errorEntryR i j * x j‖ := norm_sum_le _ _
    _ = ∑ j : I, |(errorEntryQ i j : ℝ)| * ‖x j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ j : I, |(errorEntryQ i j : ℝ)| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (↑(∑ j : I, |errorEntryQ i j|) : ℝ) * ‖x‖ := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (inverseErrorTotal : ℝ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (error_row_le_total i)) (norm_nonneg _)

lemma preconditioner_mul_jacobian_injective :
    Function.Injective fun x : V => preconditionerR *ᵥ (jacobianR *ᵥ x) := by
  intro x y hxy
  change preconditionerR *ᵥ (jacobianR *ᵥ x) =
    preconditionerR *ᵥ (jacobianR *ᵥ y) at hxy
  have hzero : preconditionerR *ᵥ (jacobianR *ᵥ (x - y)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, hxy, sub_self]
  have hbound := sub_mulVec_mulVec_norm_le (x - y)
  rw [hzero, sub_zero] at hbound
  have hq : (inverseErrorTotal : ℝ) < 1 := by
    exact (Rat.cast_lt.mpr inverseErrorTotal_lt_half).trans_le (by norm_num)
  have hz : ‖x - y‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have := (mul_lt_mul_of_pos_right hq hp)
    exact (not_lt_of_ge hbound) (by simpa using this)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma jacobian_mulVec_injective : Function.Injective jacobianR.mulVec := by
  intro x y hxy
  apply preconditioner_mul_jacobian_injective
  change preconditionerR *ᵥ (jacobianR *ᵥ x) =
    preconditionerR *ᵥ (jacobianR *ᵥ y)
  rw [hxy]

lemma jacobian_mulVec_surjective : Function.Surjective jacobianR.mulVec := by
  change Function.Surjective jacobianR.mulVecLin
  exact LinearMap.injective_iff_surjective.mp jacobian_mulVec_injective

lemma preconditioner_mulVec_injective : Function.Injective preconditionerR.mulVec := by
  intro x y hxy
  obtain ⟨u, hu⟩ := jacobian_mulVec_surjective (x - y)
  have hzero : preconditionerR *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hcomp : preconditionerR *ᵥ (jacobianR *ᵥ u) = 0 := by simpa [hu] using hzero
  have hcomp' : (fun v : V => preconditionerR *ᵥ (jacobianR *ᵥ v)) u =
      (fun v : V => preconditionerR *ᵥ (jacobianR *ᵥ v)) 0 := by
    simpa using hcomp
  have hu0 : u = 0 := preconditioner_mul_jacobian_injective hcomp'
  have : x - y = 0 := by rw [← hu, hu0]; simp
  exact sub_eq_zero.mp this

#print axioms preconditioner_mulVec_injective

end LittlewoodCylinders.LowerCertificate
