import UpperNoParallel
import UpperRecordedCases

/-! Extract the sign system from the actual affine-line formulation.
Nonparallelism and independence of triples follow from the distance hypotheses.
No generic-position assumption is needed in the final bridge theorem. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open LittlewoodCylinders.LineGeometry

noncomputable def realSign (x : ℝ) : ℤ := if x < 0 then -1 else 1

theorem realSign_values (x : ℝ) : realSign x = 1 ∨ realSign x = -1 := by
  unfold realSign
  split_ifs <;> simp

theorem realSign_mul_eq_abs (x : ℝ) : (realSign x : ℝ) * x = |x| := by
  unfold realSign
  split_ifs with h
  · simp [abs_of_neg h]
  · simp [abs_of_nonneg (le_of_not_gt h)]

theorem eq_realSign_mul {x r : ℝ} (h : |x| = r) : x = (realSign x : ℝ) * r := by
  rw [← h]
  unfold realSign
  split_ifs with hneg
  · simp [abs_of_neg hneg]
  · simp [abs_of_nonneg (le_of_not_gt hneg)]

theorem cross_ne_zero_of_directions_ne {p q u v : Space} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdir : (affineLine p u).direction ≠ (affineLine q v).direction) : cross u v ≠ 0 := by
  intro hz
  have hscale := eq_smul_of_cross_eq_zero hu hz
  have ha : ⟪u, v⟫ / ⟪u, u⟫ ≠ 0 := by
    intro ha
    apply hv
    rw [hscale, ha, zero_smul]
  apply hdir
  rw [direction_affineLine, direction_affineLine, hscale]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) u).symm

/-- The finite sign data of a family of nonparallel unit-distance axes.
The diagonal contact signs are zero and every off-diagonal sign is ±1. -/
theorem signs_of_nonparallel_axes (p u : Fin 8 → Space)
    (hcross : ∀ i j, i ≠ j → cross (u i) (u j) ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ SignRealizable E χ := by
  classical
  let m := fun k => cross (p k) (u k)
  let E := fun i j => if i = j then (0 : ℤ) else realSign (contact u m i j)
  let χ := fun a b c => realSign (triple (u a) (u b) (u c))
  refine ⟨E, χ, ?_, ?_, ?_, ?_, u, m, ?_, ?_⟩
  · intro i
    simp [E]
  · intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [E, if_neg hij, if_neg (Ne.symm hij), contact_symmetric u m i j]
  · intro i j hij
    simpa only [E, if_neg hij] using realSign_values (contact u m i j)
  · intro a b c
    exact realSign_values _
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [E, m, contact_of_moments]
    · simp only [E, if_neg hij]
      exact eq_realSign_mul (contact_magnitude_of_unit_distance p u i j
        (hcross i j hij) (hdist i j hij))
  · intro a b c hab hbc
    rw [show (χ a b c : ℝ) = (realSign (triple (u a) (u b) (u c)) : ℝ) from rfl,
      realSign_mul_eq_abs]
    exact abs_pos.mpr (uniform_of_nonparallel_unit_distances p u hcross hdist
      a b c hab.ne (lt_trans hab hbc).ne hbc.ne)

/-- A version of the bridge with explicit pairwise nonparallelism. -/
theorem signs_of_nonparallel_affine_configuration
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1)
    (hparallel : ∀ i j, i ≠ j → (L i).direction ≠ (L j).direction) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ SignRealizable E χ := by
  obtain ⟨p, u, hu, hL⟩ := exists_family_parameters L hdim
  apply signs_of_nonparallel_axes p u
  · intro i j hij
    have hdir : (affineLine (p i) (u i)).direction ≠
        (affineLine (p j) (u j)).direction := by
      rw [← hL i, ← hL j]
      exact hparallel i j hij
    exact cross_ne_zero_of_directions_ne (hu i) (hu j) hdir
  · intro i j hij
    simpa only [hL, lineDistance] using hdist i j hij

/-- Every hypothetical eight-axis configuration in the original conjecture
produces a uniform sign system. This includes all degenerate cases: parallel
pairs and dependent triples have been excluded from the distance assumptions. -/
theorem signs_of_affine_configuration
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ SignRealizable E χ := by
  obtain ⟨p, u, hu, hL⟩ := exists_family_parameters L hdim
  have hd : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1 := by
    intro i j hij
    simpa only [hL, lineDistance] using hdist i j hij
  exact signs_of_nonparallel_axes p u (no_parallel_in_eight p u hu hd) hd

#print axioms signs_of_affine_configuration

end LittlewoodCylinders.Upper
