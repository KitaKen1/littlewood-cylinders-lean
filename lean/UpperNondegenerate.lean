import UpperDistance

/-! Nondegeneracy consequences of the actual distance hypotheses. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open LittlewoodCylinders.LineGeometry

/-- Three points on a real line cannot be pairwise at the same positive distance. -/
theorem no_three_equal_distances_on_line (a b c r : ℝ) (hr : 0 < r)
    (hab : |b - a| = r) (hac : |c - a| = r) (hbc : |c - b| = r) : False := by
  rcases (abs_eq hr.le).mp hab with hab | hab <;>
    rcases (abs_eq hr.le).mp hac with hac | hac <;>
      rcases (abs_eq hr.le).mp hbc with hbc | hbc <;> linarith

theorem triple_cyclic (a b c : Space) : triple a b c = triple c a b := by
  simp only [triple]
  ring

/-- Three pairwise nonparallel unit-distance axes have independent directions.
The proof converts a common normal into three heights on a real line. -/
theorem triple_ne_zero_of_unit_distances (p q r u v w : Space)
    (huv : cross u v ≠ 0) (huw : cross u w ≠ 0) (hvw : cross v w ≠ 0)
    (hpq : lineDistance p u q v = 1)
    (hpr : lineDistance p u r w = 1)
    (hqr : lineDistance q v r w = 1) : triple u v w ≠ 0 := by
  intro hzero
  let n := cross u v
  have hn : n ≠ 0 := huv
  have hun : ⟪u, n⟫ = 0 := inner_cross_left u v
  have hvn : ⟪v, n⟫ = 0 := inner_cross_right u v
  have hwn : ⟪w, n⟫ = 0 := by
    rw [inner_cross_eq_triple, ← triple_cyclic u v w]
    exact hzero
  have hnp : 0 < ‖n‖ := norm_pos_iff.mpr hn
  rw [lineDistance_eq_normal p q u v n huv hn hun hvn] at hpq
  rw [lineDistance_eq_normal p r u w n huw hn hun hwn] at hpr
  rw [lineDistance_eq_normal q r v w n hvw hn hvn hwn] at hqr
  have hab : |⟪q, n⟫ - ⟪p, n⟫| = ‖n‖ := by
    simpa only [inner_sub_left, one_mul] using (div_eq_iff hnp.ne').mp hpq
  have hac : |⟪r, n⟫ - ⟪p, n⟫| = ‖n‖ := by
    simpa only [inner_sub_left, one_mul] using (div_eq_iff hnp.ne').mp hpr
  have hbc : |⟪r, n⟫ - ⟪q, n⟫| = ‖n‖ := by
    simpa only [inner_sub_left, one_mul] using (div_eq_iff hnp.ne').mp hqr
  exact no_three_equal_distances_on_line _ _ _ _ hnp hab hac hbc

theorem uniform_of_nonparallel_unit_distances {ι : Type*} (p u : ι → Space)
    (hcross : ∀ i j, i ≠ j → cross (u i) (u j) ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1) :
    ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0 := by
  intro a b c hab hac hbc
  exact triple_ne_zero_of_unit_distances _ _ _ _ _ _
    (hcross a b hab) (hcross a c hac) (hcross b c hbc)
    (hdist a b hab) (hdist a c hac) (hdist b c hbc)

#print axioms uniform_of_nonparallel_unit_distances

end LittlewoodCylinders.Upper
