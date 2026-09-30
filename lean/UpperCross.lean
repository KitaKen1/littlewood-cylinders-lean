import Mathlib

/-! Small coordinate identities used by the geometric upper bound. -/

namespace LittlewoodCylinders.Upper

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def cross (a b : Space) : Space :=
  WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

noncomputable def triple (a b c : Space) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) +
  a 1 * (b 2 * c 0 - b 0 * c 2) +
  a 2 * (b 0 * c 1 - b 1 * c 0)

theorem cross_add_left (a b c : Space) : cross (a + b) c = cross a c + cross b c := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

theorem cross_add_right (a b c : Space) : cross a (b + c) = cross a b + cross a c := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

theorem cross_smul_left (t : ℝ) (a b : Space) : cross (t • a) b = t • cross a b := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

theorem cross_smul_right (t : ℝ) (a b : Space) : cross a (t • b) = t • cross a b := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

@[simp] theorem cross_self (a : Space) : cross a a = 0 := by
  ext k
  fin_cases k <;> simp [cross] <;> ring

@[simp] theorem cross_zero (a : Space) : cross a 0 = 0 := by
  ext k
  fin_cases k <;> simp [cross]

/-- The alternating cofactor relation of four directions. -/
theorem cofactor_relation (a b c d : Space) :
    triple b c d • a - triple a c d • b + triple a b d • c - triple a b c • d = 0 := by
  ext k
  fin_cases k <;> simp [triple] <;> ring

/-- Two cross products with the same first factor. -/
theorem cross_cross_common (a b c : Space) :
    cross (cross a b) (cross a c) = triple a b c • a := by
  ext k
  fin_cases k <;> simp [cross, triple] <;> ring

theorem triple_ne_zero_left {a b c : Space} (h : triple a b c ≠ 0) : a ≠ 0 := by
  intro ha
  apply h
  simp [triple, ha]

/-- Nonzero triple determinant implies strict triangle inequality for any
nonzero rescalings of the corresponding two projected edges. -/
theorem projected_edges_not_collinear (a b c : Space) (s t : ℝ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hdet : triple a b c ≠ 0) :
    ‖t • cross a c‖ • (s • cross a b) ≠
      ‖s • cross a b‖ • (t • cross a c) := by
  have hcross : cross (s • cross a b) (t • cross a c) ≠ 0 := by
    rw [cross_smul_left, cross_smul_right, cross_cross_common]
    exact smul_ne_zero hs (smul_ne_zero ht (smul_ne_zero hdet (triple_ne_zero_left hdet)))
  have hb : s • cross a b ≠ 0 := by
    intro hz
    apply hcross
    rw [hz]
    ext k
    fin_cases k <;> simp [cross]
  intro heq
  have hh := congrArg (fun z => cross (s • cross a b) z) heq
  rw [cross_smul_right, cross_self, smul_zero, cross_smul_right] at hh
  exact hcross ((smul_eq_zero.mp hh.symm).resolve_left (norm_ne_zero_iff.mpr hb))

#print axioms cofactor_relation
#print axioms projected_edges_not_collinear

end LittlewoodCylinders.Upper
