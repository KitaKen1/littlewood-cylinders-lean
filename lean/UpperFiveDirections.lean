import UpperNormObstructions
import UpperMoment
import UpperCross

namespace LittlewoodCylinders.Upper

open Finset

/-- Expanding the moment identity on a four-term dependency. -/
theorem four_contact_identity (u m : Fin 4 → Space) (a b c : ℝ)
    (hrel : a • u 0 + b • u 1 + c • u 2 - u 3 = 0)
    (hdiag : ∀ i, contact u m i i = 0) :
    a * b * contact u m 0 1 + a * c * contact u m 0 2 +
      b * c * contact u m 1 2 - a * contact u m 0 3 -
      b * contact u m 1 3 - c * contact u m 2 3 = 0 := by
  have hr : ∑ i, (![a, b, c, -1] : Fin 4 → ℝ) i • u i = 0 := by
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hrel
  have h := contact_bilinear_zero u m ![a, b, c, -1] ![a, b, c, -1] hr hr
  simp [Fin.sum_univ_succ, hdiag] at h
  rw [contact_symmetric u m 1 0, contact_symmetric u m 2 0,
    contact_symmetric u m 2 1, contact_symmetric u m 3 0,
    contact_symmetric u m 3 1, contact_symmetric u m 3 2] at h
  linarith

/-- Five normalized directions with the forbidden nine contact signs cannot
have a moment realization. The normalization-to-signs step is separate. -/
theorem five_direction_obstruction (u m : Fin 5 → Space) (x y : ℝ)
    (hx : 0 < x) (hx₁ : x < 1) (hy : 1 < y)
    (h₃ : u 3 = u 0 + u 1 + u 2)
    (h₄ : u 4 = x • u 0 + y • u 1 + u 2)
    (hne : cross (u 0) (u 3) ≠ 0)
    (hdiag : ∀ i, contact u m i i = 0)
    (hT : ∀ i j : Fin 5, i < j → i < 3 →
      contact u m i j = (if i = 0 ∧ j = 3 then -1 else 1) * ‖cross (u i) (u j)‖) :
    False := by
  let a := cross (u 1) (u 2)
  let b := -cross (u 0) (u 2)
  let c := cross (u 0) (u 1)
  have hcross₀₃ : cross (u 0) (u 3) = -(b - c) := by
    rw [h₃]
    ext k
    fin_cases k <;> simp [cross, b, c] <;> ring
  have hcross₁₃ : cross (u 1) (u 3) = a - c := by
    rw [h₃]
    ext k
    fin_cases k <;> simp [cross, a, c] <;> ring
  have hcross₂₃ : cross (u 2) (u 3) = -(a - b) := by
    rw [h₃]
    ext k
    fin_cases k <;> simp [cross, a, b] <;> ring
  have hcross₁₄ : cross (u 1) (u 4) = a - x • c := by
    rw [h₄]
    ext k
    fin_cases k <;> simp [cross, a, c] <;> ring
  have hcross₂₄ : cross (u 2) (u 4) = -(y • a - x • b) := by
    rw [h₄]
    ext k
    fin_cases k <;> simp [cross, a, b] <;> ring
  have hbc : b ≠ c := by
    intro hh
    apply hne
    rw [hcross₀₃, hh, sub_self, neg_zero]
  have hbase := four_contact_identity
    (fun i => u (![0, 1, 2, 3] i)) (fun i => m (![0, 1, 2, 3] i)) 1 1 1
    (by simp [h₃]) (fun i => hdiag _)
  have hextra := four_contact_identity
    (fun i => u (![0, 1, 2, 4] i)) (fun i => m (![0, 1, 2, 4] i)) x y 1
    (by simp [h₄]) (fun i => hdiag _)
  change 1 * 1 * contact u m 0 1 + 1 * 1 * contact u m 0 2 +
    1 * 1 * contact u m 1 2 - 1 * contact u m 0 3 -
    1 * contact u m 1 3 - 1 * contact u m 2 3 = 0 at hbase
  change x * y * contact u m 0 1 + x * 1 * contact u m 0 2 +
    y * 1 * contact u m 1 2 - x * contact u m 0 4 -
    y * contact u m 1 4 - 1 * contact u m 2 4 = 0 at hextra
  have h01 := hT 0 1 (by decide) (by decide)
  have h02 := hT 0 2 (by decide) (by decide)
  have h12 := hT 1 2 (by decide) (by decide)
  have h03 := hT 0 3 (by decide) (by decide)
  have h13 := hT 1 3 (by decide) (by decide)
  have h23 := hT 2 3 (by decide) (by decide)
  have h04 := hT 0 4 (by decide) (by decide)
  have h14 := hT 1 4 (by decide) (by decide)
  have h24 := hT 2 4 (by decide) (by decide)
  simp only [hcross₀₃, norm_neg] at h03
  simp only [hcross₁₃] at h13
  simp only [hcross₂₃, norm_neg] at h23
  simp only [hcross₁₄] at h14
  simp only [hcross₂₄, norm_neg] at h24
  norm_num at h01 h02 h12 h03 h13 h23 h04 h14 h24
  rw [h01, h02, h12, h03, h13, h23] at hbase
  rw [h01, h02, h12, h04, h14, h24] at hextra
  apply five_norm_obstruction a b c x y ‖cross (u 0) (u 4)‖ hx hx₁ hy hbc (norm_nonneg _)
  · dsimp [a, b, c] at *
    simp only [norm_neg] at *
    linarith
  · dsimp [a, b, c] at *
    simp only [norm_neg] at *
    linarith only [hextra]

#print axioms four_contact_identity
#print axioms five_direction_obstruction

end LittlewoodCylinders.Upper
