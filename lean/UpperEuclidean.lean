import UpperCross
import UpperMoment

/-! Euclidean identities for the distance and nondegeneracy arguments. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace

theorem inner_coordinates (a b : Space) :
    ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem inner_cross_left (u v : Space) : ⟪u, cross u v⟫ = 0 := by
  simp [inner_coordinates, cross, Matrix.cons_val_two]
  ring

theorem inner_cross_right (u v : Space) : ⟪v, cross u v⟫ = 0 := by
  simp [inner_coordinates, cross, Matrix.cons_val_two]
  ring

theorem inner_cross_eq_triple (a b c : Space) : ⟪a, cross b c⟫ = triple a b c := by
  simp [inner_coordinates, cross, triple, Matrix.cons_val_two]

theorem cross_reverse (u v : Space) : cross v u = -cross u v := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

theorem cross_cross_right (u v n : Space) :
    cross (cross u v) n = ⟪u, n⟫ • v - ⟪v, n⟫ • u := by
  ext k
  fin_cases k <;> simp [cross, inner_coordinates, Matrix.cons_val_two] <;> ring

theorem inner_self_pos {u : Space} (hu : u ≠ 0) : 0 < ⟪u, u⟫ := by
  rw [real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hu)

theorem eq_smul_of_cross_eq_zero {u v : Space} (hu : u ≠ 0) (hcross : cross u v = 0) :
    v = (⟪u, v⟫ / ⟪u, u⟫) • u := by
  have hh := cross_cross_right u v u
  rw [hcross, cross_reverse, cross_zero, neg_zero] at hh
  have hh' : ⟪u, u⟫ • v = ⟪u, v⟫ • u := by
    rw [real_inner_comm u v] at hh
    exact sub_eq_zero.mp hh.symm
  have h := congrArg (fun z : Space => (⟪u, u⟫)⁻¹ • z) hh'
  simp only [smul_smul, inv_mul_cancel₀ (inner_self_pos hu).ne', one_smul] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The explicit closest-point displacement for two nonparallel directions.
The separate scalar `D` keeps denominator clearing small. -/
theorem closest_displacement (p q u v : Space) (D : ℝ) (hD : D ≠ 0)
    (hDdef : D = ⟪cross u v, cross u v⟫) :
    let d := q - p
    let s := (⟪v, v⟫ * ⟪d, u⟫ - ⟪u, v⟫ * ⟪d, v⟫) / D
    let t := (⟪u, v⟫ * ⟪d, u⟫ - ⟪u, u⟫ * ⟪d, v⟫) / D
    (q + t • v) - (p + s • u) = (⟪d, cross u v⟫ / D) • cross u v := by
  dsimp only
  simp only [inner_coordinates] at hDdef ⊢
  ext k
  change q k + _ * v k - (p k + _ * u k) = _ * (cross u v) k
  field_simp [hD]
  rw [hDdef]
  fin_cases k <;> simp [cross, Matrix.cons_val_two] <;> ring

/-- Moments of actual axes give the signed numerator of the distance formula. -/
theorem contact_of_moments {ι : Type*} (p u : ι → Space) (i j : ι) :
    contact u (fun k => cross (p k) (u k)) i j =
      ⟪p i - p j, cross (u i) (u j)⟫ := by
  simp [contact, inner_coordinates, cross, Matrix.cons_val_two]
  ring

#print axioms closest_displacement
#print axioms contact_of_moments

end LittlewoodCylinders.Upper
