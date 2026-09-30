import Mathlib

namespace LittlewoodCylinders.LineGeometry

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def affineLine (p u : E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' p (ℝ ∙ u)

lemma direction_affineLine (p u : E) : (affineLine p u).direction = ℝ ∙ u := by
  simp [affineLine]

lemma mem_affineLine_iff {p u x : E} :
    x ∈ affineLine p u ↔ ∃ a : ℝ, p + a • u = x := by
  rw [affineLine, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have ha' : a • u + p = x := (eq_sub_iff_add_eq).mp ha
    simpa [add_comm] using ha'
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp

lemma finrank_direction_affineLine {p u : E} (hu : u ≠ 0) :
    Module.finrank ℝ (affineLine p u).direction = 1 := by
  rw [direction_affineLine, finrank_span_singleton hu]

lemma inner_line_difference {p q u v n x y : E}
    (hun : ⟪u, n⟫ = 0) (hvn : ⟪v, n⟫ = 0)
    (hx : x ∈ affineLine p u) (hy : y ∈ affineLine q v) :
    ⟪y - x, n⟫ = ⟪q - p, n⟫ := by
  obtain ⟨a, rfl⟩ := mem_affineLine_iff.mp hx
  obtain ⟨b, rfl⟩ := mem_affineLine_iff.mp hy
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hun, hvn,
    mul_zero, add_zero]

lemma line_distance_lower_bound {p q u v n x y : E}
    (hn : 0 < ‖n‖)
    (hun : ⟪u, n⟫ = 0) (hvn : ⟪v, n⟫ = 0)
    (hsep : |⟪q - p, n⟫| = ‖n‖)
    (hx : x ∈ affineLine p u) (hy : y ∈ affineLine q v) :
    1 ≤ dist x y := by
  have hcs := abs_real_inner_le_norm (y - x) n
  rw [inner_line_difference hun hvn hx hy, hsep] at hcs
  rw [dist_eq_norm]
  have hnorm : ‖y - x‖ = ‖x - y‖ := by rw [← norm_neg, neg_sub]
  rw [hnorm] at hcs
  nlinarith

noncomputable def lineDistance (p u q v : E) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ affineLine p u, ∃ y ∈ affineLine q v, dist x y = r}

lemma lineDistance_comm (p u q v : E) :
    lineDistance p u q v = lineDistance q v p u := by
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, by simpa [dist_comm] using hxy⟩
  · rintro ⟨y, hy, x, hx, hyx⟩
    exact ⟨x, hx, y, hy, by simpa [dist_comm] using hyx⟩

lemma lineDistance_eq_one {p q u v n : E}
    (hn : 0 < ‖n‖)
    (hun : ⟪u, n⟫ = 0) (hvn : ⟪v, n⟫ = 0)
    (hsep : |⟪q - p, n⟫| = ‖n‖)
    (hwitness : ∃ x ∈ affineLine p u, ∃ y ∈ affineLine q v, dist x y = 1) :
    lineDistance p u q v = 1 := by
  apply le_antisymm
  · exact csInf_le
      ⟨0, by rintro r ⟨x, hx, y, hy, rfl⟩; exact dist_nonneg⟩
      hwitness
  · apply le_csInf
    · exact ⟨1, hwitness⟩
    · rintro r ⟨x, hx, y, hy, rfl⟩
      exact line_distance_lower_bound hn hun hvn hsep hx hy

/-- A displacement perpendicular to both directions attains the infimum.
This includes intersecting lines and parallel lines. -/
theorem lineDistance_eq_dist_of_orthogonal {p q u v x y : E}
    (hx : x ∈ affineLine p u) (hy : y ∈ affineLine q v)
    (hu : ⟪u, y - x⟫ = 0) (hv : ⟪v, y - x⟫ = 0) :
    lineDistance p u q v = dist x y := by
  apply le_antisymm
  · exact csInf_le
      ⟨0, by rintro r ⟨a, ha, b, hb, rfl⟩; exact dist_nonneg⟩
      ⟨x, hx, y, hy, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨dist x y, x, hx, y, hy, rfl⟩
    rintro r ⟨a, ha, b, hb, rfl⟩
    have hi : ⟪b - a, y - x⟫ = ‖y - x‖ ^ 2 := by
      rw [inner_line_difference hu hv ha hb,
        ← inner_line_difference hu hv hx hy, real_inner_self_eq_norm_sq]
    have hcs := abs_real_inner_le_norm (b - a) (y - x)
    rw [hi, abs_of_nonneg (sq_nonneg _)] at hcs
    have hn : ‖y - x‖ ≤ ‖b - a‖ := by
      by_cases hz : ‖y - x‖ = 0
      · rw [hz]
        exact norm_nonneg _
      · have hp := lt_of_le_of_ne (norm_nonneg (y - x)) (Ne.symm hz)
        nlinarith
    simpa only [dist_eq_norm, norm_sub_rev] using hn

#print axioms lineDistance_eq_dist_of_orthogonal

#print axioms lineDistance_eq_one

end LittlewoodCylinders.LineGeometry
