import Mathlib

/-!
Metric obstructions for the upper bound. These are independent of the finite
enumeration and of the lower-bound certificate. No normalization of the norm or
choice of Euclidean coordinates is required for the five-direction inequality.
-/

namespace LittlewoodCylinders.Upper

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The arithmetic certificate for the five-direction obstruction. -/
theorem five_length_obstruction (x y K A B C D F S₀ S₁ S₂ : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hB : 0 < B) (hS₀ : 0 ≤ S₀)
    (hbase : D + F = K + A + B + C)
    (hextra : x * S₀ + y * S₁ + S₂ = x * y * K + x * A + y * C)
    (htri₁ : D ≤ S₁ + (1 - x) * K)
    (htri₂ : y * F ≤ S₂ + (y - x) * A) : False := by
  have h₁ := mul_nonneg hy.le (sub_nonneg.mpr htri₁)
  have h₂ := mul_nonneg hx.le hS₀
  have h₃ := mul_pos hy hB
  have hbase' := congrArg (fun z : ℝ => y * z) hbase
  nlinarith

/-- Five-direction metric obstruction, valid in any real normed space.
The vectors `a,b,c` represent the images of the three basis bivectors under
one common linear map. Its norm need not satisfy `‖c‖ = 1`. -/
theorem five_norm_obstruction (a b c : V) (x y S₀ : ℝ)
    (hx : 0 < x) (hx₁ : x < 1) (hy : 1 < y)
    (hbc : b ≠ c) (hS₀ : 0 ≤ S₀)
    (hbase : ‖a - c‖ + ‖a - b‖ = ‖c‖ + ‖b‖ + ‖b - c‖ + ‖a‖)
    (hextra : x * S₀ + y * ‖a - x • c‖ + ‖y • a - x • b‖ =
      x * y * ‖c‖ + x * ‖b‖ + y * ‖a‖) : False := by
  have htri₁ : ‖a - c‖ ≤ ‖a - x • c‖ + (1 - x) * ‖c‖ := by
    have hid : a - c = (a - x • c) - (1 - x) • c := by module
    rw [hid]
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx₁)] using
      norm_sub_le (a - x • c) ((1 - x) • c)
  have htri₂ : y * ‖a - b‖ ≤ ‖y • a - x • b‖ + (y - x) * ‖b‖ := by
    have hid : y • (a - b) = (y • a - x • b) - (y - x) • b := by module
    have h := norm_sub_le (y • a - x • b) ((y - x) • b)
    rw [← hid] at h
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < y),
      abs_of_pos (by linarith : 0 < y - x)] using h
  exact five_length_obstruction x y ‖c‖ ‖b‖ ‖b - c‖ ‖a‖ ‖a - c‖
    ‖a - b‖ S₀ ‖a - x • c‖ ‖y • a - x • b‖ hx (by linarith)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hbc)) hS₀ hbase hextra htri₁ htri₂

end Normed

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Strict triangle inequality, with its exact noncollinearity hypothesis. -/
theorem strict_triangle {a b : V} (h : ‖b‖ • a ≠ ‖a‖ • b) :
    ‖a + b‖ < ‖a‖ + ‖b‖ :=
  lt_of_le_of_ne (norm_add_le a b) (fun heq => h (norm_add_eq_iff_real.mp heq))

/-- Three closed edges: the sum with one minus sign is positive. -/
theorem closed_triangle_majority {a b c : V}
    (hclosed : a + b + c = 0) (h : ‖b‖ • a ≠ ‖a‖ • b) :
    0 < ‖a‖ + ‖b‖ - ‖c‖ := by
  have hc : c = -(a + b) := eq_neg_of_add_eq_zero_right hclosed
  rw [hc, norm_neg]
  exact sub_pos.mpr (strict_triangle h)

/-- Four closed edges: two noncollinear positive edges already make the
three-to-one majority strict. -/
theorem closed_quadrilateral_majority {a b c d : V}
    (hclosed : a + b + c + d = 0) (h : ‖b‖ • a ≠ ‖a‖ • b) :
    0 < ‖a‖ + ‖b‖ + ‖c‖ - ‖d‖ := by
  have hd : d = -(a + b + c) := eq_neg_of_add_eq_zero_right hclosed
  rw [hd, norm_neg]
  have hle := norm_add_le (a + b) c
  have hlt := strict_triangle h
  linarith

end Inner

#print axioms five_norm_obstruction
#print axioms closed_triangle_majority
#print axioms closed_quadrilateral_majority

end LittlewoodCylinders.Upper
