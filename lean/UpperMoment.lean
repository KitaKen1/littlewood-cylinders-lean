import Mathlib

/-! Position elimination: the contact matrix vanishes between any two
linear dependencies of the directions. This identity is the algebraic input
to both the five-direction and closed-polygon obstructions. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open Finset

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Moment pairing; geometrically `m i = p i × u i`. -/
noncomputable def contact (u m : ι → V) (i j : ι) : ℝ :=
  ⟪u i, m j⟫ + ⟪m i, u j⟫

omit [Fintype ι] in
theorem contact_symmetric (u m : ι → V) (i j : ι) :
    contact u m i j = contact u m j i := by
  simp only [contact, real_inner_comm]
  ring

/-- This version allows two separately indexed dependencies, avoiding
padding four-term circuits with zeros. -/
theorem moment_bilinear_zero (u m : ι → V) (v n : κ → V)
    (c : ι → ℝ) (d : κ → ℝ)
    (hc : ∑ i, c i • u i = 0) (hd : ∑ j, d j • v j = 0) :
    ∑ j, d j * (∑ i, c i * (⟪v j, m i⟫ + ⟪n j, u i⟫)) = 0 := by
  have hrow (j : κ) :
      ∑ i, c i * (⟪v j, m i⟫ + ⟪n j, u i⟫) =
      ⟪v j, ∑ i, c i • m i⟫ := by
    simp_rw [mul_add, sum_add_distrib, ← real_inner_smul_right, ← inner_sum]
    rw [hc, inner_zero_right, add_zero]
  simp_rw [hrow, ← real_inner_smul_left, ← sum_inner]
  rw [hd, inner_zero_left]

theorem contact_bilinear_zero (u m : ι → V) (c d : ι → ℝ)
    (hc : ∑ i, c i • u i = 0) (hd : ∑ i, d i • u i = 0) :
    ∑ j, d j * (∑ i, c i * contact u m j i) = 0 :=
  moment_bilinear_zero u m u m c d hc hd

/-- If all products between two circuit rows have one strict sign, the
moment factorization is impossible. -/
theorem circuit_obstruction [Nonempty κ]
    (u m : ι → V) (v n : κ → V) (c : ι → ℝ) (d : κ → ℝ)
    (hc : ∑ i, c i • u i = 0) (hd : ∑ j, d j • v j = 0)
    (hpos : ∀ j, 0 < d j * (∑ i, c i * (⟪v j, m i⟫ + ⟪n j, u i⟫))) :
    False := by
  have hp := sum_pos (fun j (_ : j ∈ (univ : Finset κ)) => hpos j) univ_nonempty
  rw [moment_bilinear_zero u m v n c d hc hd] at hp
  exact (lt_irrefl 0) hp

#print axioms moment_bilinear_zero
#print axioms circuit_obstruction

end LittlewoodCylinders.Upper
