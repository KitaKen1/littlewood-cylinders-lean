import UpperEuclidean
import AxisParametrization

/-! Distance formulas for arbitrary affine axes, using the same infimum as
the final conjecture statement. The nearest points are explicit witnesses. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open LittlewoodCylinders.LineGeometry

theorem lineDistance_eq_cross (p q u v : Space) (hcross : cross u v ≠ 0) :
    lineDistance p u q v = |⟪q - p, cross u v⟫| / ‖cross u v‖ := by
  let n := cross u v
  let D := ⟪n, n⟫
  let d := q - p
  let s := (⟪v, v⟫ * ⟪d, u⟫ - ⟪u, v⟫ * ⟪d, v⟫) / D
  let t := (⟪u, v⟫ * ⟪d, u⟫ - ⟪u, u⟫ * ⟪d, v⟫) / D
  let x := p + s • u
  let y := q + t • v
  have hD : 0 < D := inner_self_pos hcross
  have hn : 0 < ‖n‖ := norm_pos_iff.mpr hcross
  have hdisp : y - x = (⟪d, n⟫ / D) • n :=
    closest_displacement p q u v D hD.ne' rfl
  have hx : x ∈ affineLine p u := mem_affineLine_iff.mpr ⟨s, rfl⟩
  have hy : y ∈ affineLine q v := mem_affineLine_iff.mpr ⟨t, rfl⟩
  have hu : ⟪u, y - x⟫ = 0 := by
    rw [hdisp, real_inner_smul_right, inner_cross_left, mul_zero]
  have hv : ⟪v, y - x⟫ = 0 := by
    rw [hdisp, real_inner_smul_right, inner_cross_right, mul_zero]
  rw [lineDistance_eq_dist_of_orthogonal hx hy hu hv, dist_eq_norm,
    norm_sub_rev, hdisp, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hD]
  change |⟪d, n⟫| / D * ‖n‖ = |⟪d, n⟫| / ‖n‖
  have hDsq : D = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
  rw [hDsq]
  field_simp [hn.ne']

/-- Any nonzero common normal gives the same distance formula. -/
theorem lineDistance_eq_normal (p q u v n : Space) (hcross : cross u v ≠ 0)
    (hn : n ≠ 0) (hun : ⟪u, n⟫ = 0) (hvn : ⟪v, n⟫ = 0) :
    lineDistance p u q v = |⟪q - p, n⟫| / ‖n‖ := by
  have hzero : cross (cross u v) n = 0 := by
    rw [cross_cross_right, hun, hvn, zero_smul, zero_smul, sub_self]
  let a := ⟪cross u v, n⟫ / ⟪cross u v, cross u v⟫
  have hscale : n = a • cross u v := eq_smul_of_cross_eq_zero hcross hzero
  have ha : a ≠ 0 := by
    intro hz
    apply hn
    rw [hscale, hz, zero_smul]
  rw [lineDistance_eq_cross p q u v hcross, hscale,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_mul]
  field_simp [abs_ne_zero.mpr ha, norm_ne_zero_iff.mpr hcross]

/-- Parallel axes: subtract the component of their displacement along the
common direction. This also covers coincident axes. -/
theorem lineDistance_parallel (p q u : Space) (hu : u ≠ 0) :
    lineDistance p u q u = ‖(q - p) - (⟪q - p, u⟫ / ⟪u, u⟫) • u‖ := by
  let s := ⟪q - p, u⟫ / ⟪u, u⟫
  have hx : p + s • u ∈ affineLine p u := mem_affineLine_iff.mpr ⟨s, rfl⟩
  have hy : q ∈ affineLine q u := mem_affineLine_iff.mpr ⟨0, by simp⟩
  have hperp : ⟪u, q - (p + s • u)⟫ = 0 := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, s,
      inner_sub_left]
    rw [real_inner_comm q u, real_inner_comm p u]
    field_simp [(inner_self_pos hu).ne']
    ring
  rw [lineDistance_eq_dist_of_orthogonal hx hy hperp hperp, dist_eq_norm, norm_sub_rev]
  congr 1
  dsimp [s]
  module

theorem contact_magnitude_of_unit_distance {ι : Type*} (p u : ι → Space) (i j : ι)
    (hcross : cross (u i) (u j) ≠ 0)
    (hdist : lineDistance (p i) (u i) (p j) (u j) = 1) :
    |contact u (fun k => cross (p k) (u k)) i j| = ‖cross (u i) (u j)‖ := by
  rw [lineDistance_eq_cross _ _ _ _ hcross] at hdist
  have hh := (div_eq_iff (norm_ne_zero_iff.mpr hcross)).mp hdist
  rw [contact_of_moments]
  simpa [inner_sub_left, abs_sub_comm] using hh

#print axioms lineDistance_eq_cross
#print axioms lineDistance_eq_normal
#print axioms lineDistance_parallel
#print axioms contact_magnitude_of_unit_distance

end LittlewoodCylinders.Upper
