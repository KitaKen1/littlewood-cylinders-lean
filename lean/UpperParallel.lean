import UpperNondegenerate

/-! Parallel-axis geometry. All projections and distance comparisons are exact. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open LittlewoodCylinders.LineGeometry

noncomputable def normalPart (u x : Space) : Space :=
  x - (⟪x, u⟫ / ⟪u, u⟫) • u

theorem normalPart_sub (u x y : Space) :
    normalPart u (x - y) = normalPart u x - normalPart u y := by
  simp only [normalPart, inner_sub_left, sub_div, sub_smul]
  module

theorem normalPart_orthogonal {u : Space} (hu : u ≠ 0) (x : Space) :
    ⟪normalPart u x, u⟫ = 0 := by
  simp only [normalPart, inner_sub_left, real_inner_smul_left]
  field_simp [(inner_self_pos hu).ne']
  ring

theorem lineDistance_eq_normalPart (p q u : Space) (hu : u ≠ 0) :
    lineDistance p u q u = ‖normalPart u q - normalPart u p‖ := by
  rw [lineDistance_parallel p q u hu, ← normalPart_sub]
  rfl

theorem gram_determinant (a b c : Space) :
    (triple a b c) ^ 2 =
      ⟪a, a⟫ * ⟪b, b⟫ * ⟪c, c⟫ + 2 * ⟪a, b⟫ * ⟪a, c⟫ * ⟪b, c⟫ -
      ⟪a, a⟫ * ⟪b, c⟫ ^ 2 - ⟪b, b⟫ * ⟪a, c⟫ ^ 2 - ⟪c, c⟫ * ⟪a, b⟫ ^ 2 := by
  simp only [triple, inner_coordinates]
  ring

theorem triple_zero_of_common_orthogonal {u a b c : Space} (hu : u ≠ 0)
    (ha : ⟪a, u⟫ = 0) (hb : ⟪b, u⟫ = 0) (hc : ⟪c, u⟫ = 0) :
    triple a b c = 0 := by
  have h := congrArg (fun x : Space => ⟪x, u⟫) (cofactor_relation u a b c)
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    ha, hb, hc, mul_zero, sub_zero, add_zero, inner_zero_left] at h
  exact (mul_eq_zero.mp h).resolve_right (inner_self_pos hu).ne'

/-- Four mutually unit-separated points cannot lie in a plane with nonzero normal.
Their three displacement vectors would have Gram determinant `1/2`. -/
theorem no_four_unit_points_in_plane (p : Fin 4 → Space) (u : Space) (hu : u ≠ 0)
    (hplane : ∀ i, ⟪p i, u⟫ = 0)
    (hdist : ∀ i j, i ≠ j → ‖p j - p i‖ = 1) : False := by
  let a := p 1 - p 0
  let b := p 2 - p 0
  let c := p 3 - p 0
  have hs (i j : Fin 4) (hij : i ≠ j) : ⟪p j - p i, p j - p i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hdist i j hij]
    norm_num
  have haa : ⟪a, a⟫ = 1 := hs 0 1 (by decide)
  have hbb : ⟪b, b⟫ = 1 := hs 0 2 (by decide)
  have hcc : ⟪c, c⟫ = 1 := hs 0 3 (by decide)
  have hab : ⟪a, b⟫ = 1 / 2 := by
    have h := hs 1 2 (by decide)
    have heq : p 2 - p 1 = b - a := by dsimp [a, b]; module
    rw [heq] at h
    simp only [inner_sub_left, inner_sub_right, haa, hbb, real_inner_comm a b] at h
    linarith
  have hac : ⟪a, c⟫ = 1 / 2 := by
    have h := hs 1 3 (by decide)
    have heq : p 3 - p 1 = c - a := by dsimp [a, c]; module
    rw [heq] at h
    simp only [inner_sub_left, inner_sub_right, haa, hcc, real_inner_comm a c] at h
    linarith
  have hbc : ⟪b, c⟫ = 1 / 2 := by
    have h := hs 2 3 (by decide)
    have heq : p 3 - p 2 = c - b := by dsimp [b, c]; module
    rw [heq] at h
    simp only [inner_sub_left, inner_sub_right, hbb, hcc, real_inner_comm b c] at h
    linarith
  have hz : triple a b c = 0 := triple_zero_of_common_orthogonal hu
    (by simp [a, inner_sub_left, hplane])
    (by simp [b, inner_sub_left, hplane])
    (by simp [c, inner_sub_left, hplane])
  have hgram := gram_determinant a b c
  rw [hz, haa, hbb, hcc, hab, hac, hbc] at hgram
  norm_num at hgram

theorem no_four_parallel_axes (p : Fin 4 → Space) (u : Space) (hu : u ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) u (p j) u = 1) : False := by
  apply no_four_unit_points_in_plane (fun i => normalPart u (p i)) u hu
  · exact fun i => normalPart_orthogonal hu (p i)
  · intro i j hij
    simpa only [lineDistance_eq_normalPart (p i) (p j) u hu] using hdist i j hij

theorem same_sign_of_close (a b r : ℝ) (hr : 0 < r)
    (ha : |a| = r) (hb : |b| = r) (hab : |b - a| ≤ r) : a = b := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hab
  rcases (abs_eq hr.le).mp ha with ha | ha <;>
    rcases (abs_eq hr.le).mp hb with hb | hb <;> linarith

theorem normalPart_inner {u n : Space} (x : Space) (hn : ⟪u, n⟫ = 0) :
    ⟪normalPart u x, n⟫ = ⟪x, n⟫ := by
  simp only [normalPart, inner_sub_left, real_inner_smul_left, hn, mul_zero, sub_zero]

/-- An equilateral triple cannot have its displacement vectors perpendicular
to two nonzero orthogonal normals. -/
theorem no_three_unit_points_two_normals (p : Fin 3 → Space) (u n : Space)
    (hu : u ≠ 0) (hn : n ≠ 0) (hun : ⟪u, n⟫ = 0)
    (hp : ∀ i, ⟪p i, u⟫ = 0)
    (hq : ∀ i, ⟪p i - p 0, n⟫ = 0)
    (hdist : ∀ i j, i ≠ j → ‖p j - p i‖ = 1) : False := by
  let a := p 1 - p 0
  let b := p 2 - p 0
  have haa : ⟪a, a⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hdist 0 1 (by decide)]; norm_num
  have hbb : ⟪b, b⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hdist 0 2 (by decide)]; norm_num
  have hab : ⟪a, b⟫ = 1 / 2 := by
    have hh : ⟪b - a, b - a⟫ = 1 := by
      have heq : b - a = p 2 - p 1 := by dsimp [a, b]; module
      rw [heq, real_inner_self_eq_norm_sq, hdist 1 2 (by decide)]; norm_num
    simp only [inner_sub_left, inner_sub_right, haa, hbb, real_inner_comm a b] at hh
    linarith
  have hau : ⟪a, u⟫ = 0 := by simp [a, inner_sub_left, hp]
  have hbu : ⟪b, u⟫ = 0 := by simp [b, inner_sub_left, hp]
  have hz := triple_zero_of_common_orthogonal hn (hq 1) (hq 2) hun
  have hg := gram_determinant a b u
  rw [hz, haa, hbb, hab, hau, hbu] at hg
  have hpos := inner_self_pos hu
  nlinarith

/-- Three parallel axes at mutual distance one admit no nonparallel axis
whose distance from all three is one. -/
theorem no_three_parallel_with_transversal (p : Fin 3 → Space) (q u v : Space)
    (hu : u ≠ 0) (hcross : cross u v ≠ 0)
    (hp : ∀ i j, i ≠ j → lineDistance (p i) u (p j) u = 1)
    (hq : ∀ i, lineDistance (p i) u q v = 1) : False := by
  let n := cross u v
  have hn : 0 < ‖n‖ := norm_pos_iff.mpr hcross
  have hun : ⟪u, n⟫ = 0 := inner_cross_left u v
  have hheight (i : Fin 3) : |⟪q - p i, n⟫| = ‖n‖ := by
    have hh := hq i
    rw [lineDistance_eq_cross _ _ _ _ hcross] at hh
    simpa only [one_mul] using (div_eq_iff hn.ne').mp hh
  have hpd (i j : Fin 3) (hij : i ≠ j) :
      ‖normalPart u (p j) - normalPart u (p i)‖ = 1 := by
    simpa only [lineDistance_eq_normalPart _ _ _ hu] using hp i j hij
  apply no_three_unit_points_two_normals (fun i => normalPart u (p i)) u n hu hcross hun
  · exact fun i => normalPart_orthogonal hu (p i)
  · intro i
    by_cases hi : i = 0
    · subst i; simp
    have hcs := abs_real_inner_le_norm (normalPart u (p i) - normalPart u (p 0)) n
    rw [hpd 0 i (Ne.symm hi), one_mul, inner_sub_left,
      normalPart_inner _ hun, normalPart_inner _ hun] at hcs
    have hb : |⟪q - p i, n⟫ - ⟪q - p 0, n⟫| ≤ ‖n‖ := by
      simpa only [inner_sub_left, sub_sub_sub_cancel_left, abs_sub_comm] using hcs
    have heq := same_sign_of_close _ _ _ hn (hheight 0) (hheight i) hb
    simp only [inner_sub_left] at heq
    simp only [inner_sub_left, normalPart_inner _ hun]
    linarith
  · exact hpd

theorem affineLine_eq_of_cross_eq_zero (p : Space) {u v : Space}
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : cross u v = 0) :
    affineLine p v = affineLine p u := by
  have hs := eq_smul_of_cross_eq_zero hu hc
  have ha : ⟪u, v⟫ / ⟪u, u⟫ ≠ 0 := by
    intro hz
    apply hv
    rw [hs, hz, zero_smul]
  rw [affineLine, affineLine, hs,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha)]

theorem lineDistance_replace_left (p q v : Space) {u w : Space}
    (hu : u ≠ 0) (hw : w ≠ 0) (hc : cross u w = 0) :
    lineDistance p w q v = lineDistance p u q v := by
  unfold lineDistance
  rw [affineLine_eq_of_cross_eq_zero p hu hw hc]

theorem lineDistance_replace_right (p q v : Space) {u w : Space}
    (hu : u ≠ 0) (hw : w ≠ 0) (hc : cross u w = 0) :
    lineDistance p v q w = lineDistance p v q u := by
  unfold lineDistance
  rw [affineLine_eq_of_cross_eq_zero q hu hw hc]

/-- A unit-distance parallel pair forces every third direction into the
plane spanned by their direction and their closest displacement. -/
theorem parallel_pair_common_normal (p q u : Space) (hu : u ≠ 0)
    (hpq : lineDistance p u q u = 1) :
    ∃ n : Space, n ≠ 0 ∧ ⟪u, n⟫ = 0 ∧
      ∀ r v : Space, lineDistance p u r v = 1 → lineDistance q u r v = 1 →
        ⟪v, n⟫ = 0 := by
  let w := normalPart u (q - p)
  have hwu : ⟪w, u⟫ = 0 := normalPart_orthogonal hu _
  have hnorm : ‖w‖ = 1 := by
    rw [lineDistance_parallel p q u hu] at hpq
    exact hpq
  have hw : w ≠ 0 := by intro hz; simp [hz] at hnorm
  have hn : cross u w ≠ 0 := by
    intro hz
    have hh := eq_smul_of_cross_eq_zero hu hz
    rw [← real_inner_comm u w, hwu, zero_div, zero_smul] at hh
    exact hw hh
  refine ⟨cross u w, hn, inner_cross_left u w, ?_⟩
  intro r v hpr hqr
  by_cases huv : cross u v = 0
  · rw [eq_smul_of_cross_eq_zero hu huv, real_inner_smul_left, inner_cross_left, mul_zero]
  · have hp : 0 < ‖cross u v‖ := norm_pos_iff.mpr huv
    have ha : |⟪r - p, cross u v⟫| = ‖cross u v‖ := by
      rw [lineDistance_eq_cross _ _ _ _ huv] at hpr
      simpa only [one_mul] using (div_eq_iff hp.ne').mp hpr
    have hb : |⟪r - q, cross u v⟫| = ‖cross u v‖ := by
      rw [lineDistance_eq_cross _ _ _ _ huv] at hqr
      simpa only [one_mul] using (div_eq_iff hp.ne').mp hqr
    have hcs := abs_real_inner_le_norm w (cross u v)
    rw [hnorm, one_mul] at hcs
    have hproj : ⟪w, cross u v⟫ = ⟪q - p, cross u v⟫ :=
      normalPart_inner _ (inner_cross_left u v)
    rw [hproj] at hcs
    have hab : |⟪r - q, cross u v⟫ - ⟪r - p, cross u v⟫| ≤ ‖cross u v‖ := by
      simpa only [inner_sub_left, sub_sub_sub_cancel_left, abs_sub_comm] using hcs
    have heq := same_sign_of_close _ _ _ hp ha hb hab
    have hz : ⟪w, cross u v⟫ = 0 := by
      rw [hproj]
      simp only [inner_sub_left] at heq ⊢
      linarith
    have hswap : ⟪v, cross u w⟫ = -⟪w, cross u v⟫ := by
      simp only [inner_cross_eq_triple, triple]
      ring
    rw [hswap, hz, neg_zero]

#print axioms no_four_parallel_axes
#print axioms no_three_parallel_with_transversal
#print axioms parallel_pair_common_normal

end LittlewoodCylinders.Upper
