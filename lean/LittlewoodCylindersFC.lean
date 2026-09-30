import FormalConjecturesUtil
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic
import RootLines
import UpperSATCoverage

/-!
# Littlewood's mutually touching cylinders problem

This file states the fully inlined target and assembles the lower and upper bounds.
The upper bound combines geometric reduction, checked graph coverage, local
obstruction clauses, and LRAT refutations reconstructed as Lean proof terms.
The final axiom audit is at the end of this file.
-/

set_option autoImplicit false

namespace LittlewoodCylinders

/-- Euclidean three-space with its Euclidean norm. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- An unoriented affine line in Euclidean three-space. -/
abbrev Line3 :=
  {L : AffineSubspace ℝ E3 // Module.finrank ℝ L.direction = 1}

/-- The infimum of point-to-point distances between two axes. -/
noncomputable def axisDistance (L M : Line3) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ (L.1 : Set E3), ∃ y ∈ (M.1 : Set E3), dist x y = r}

/-- There are `n` affine lines whose pairwise distances are one. -/
def HasUnitDistanceConfiguration (n : ℕ) : Prop :=
  ∃ L : Fin n → Line3,
    Pairwise (fun i j => axisDistance (L i) (L j) = 1)

theorem line_nonempty (L : Line3) : (L.1 : Set E3).Nonempty := by
  apply (AffineSubspace.nonempty_iff_ne_bot L.1).2
  intro h
  have hdim := L.2
  change Module.finrank ℝ L.1.direction = 1 at hdim
  rw [h, AffineSubspace.direction_bot] at hdim
  simp at hdim

theorem distance_set_nonempty (L M : Line3) :
    {r : ℝ | ∃ x ∈ (L.1 : Set E3), ∃ y ∈ (M.1 : Set E3), dist x y = r}.Nonempty := by
  obtain ⟨x, hx⟩ := line_nonempty L
  obtain ⟨y, hy⟩ := line_nonempty M
  exact ⟨dist x y, x, hx, y, hy, rfl⟩

theorem distance_set_bddBelow (L M : Line3) :
    BddBelow {r : ℝ | ∃ x ∈ (L.1 : Set E3), ∃ y ∈ (M.1 : Set E3), dist x y = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact dist_nonneg

theorem axisDistance_self (L : Line3) : axisDistance L L = 0 := by
  apply le_antisymm
  · obtain ⟨x, hx⟩ := line_nonempty L
    exact csInf_le (distance_set_bddBelow L L) ⟨x, hx, x, hx, dist_self x⟩
  · apply le_csInf (distance_set_nonempty L L)
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact dist_nonneg

theorem configuration_injective {n : ℕ} (L : Fin n → Line3)
    (h : Pairwise (fun i j => axisDistance (L i) (L j) = 1)) :
    Function.Injective L := by
  intro i j heq
  by_contra hne
  have hij : axisDistance (L i) (L j) = 1 := h hne
  rw [heq, axisDistance_self] at hij
  norm_num at hij

theorem configuration_mono {m n : ℕ} (hmn : m ≤ n)
    (hn : HasUnitDistanceConfiguration n) : HasUnitDistanceConfiguration m := by
  obtain ⟨L, hL⟩ := hn
  refine ⟨fun i => L (Fin.castLE hmn i), ?_⟩
  intro i j hij
  apply hL
  intro heq
  apply hij
  apply Fin.ext
  exact congrArg (fun k : Fin n => k.val) heq

theorem greatest_iff_expanded :
    IsGreatest {n : ℕ | HasUnitDistanceConfiguration n} 7 ↔
      HasUnitDistanceConfiguration 7 ∧
        ∀ n : ℕ, HasUnitDistanceConfiguration n → n ≤ 7 := by
  rfl

theorem upper_bound_iff_no_eight :
    (∀ n : ℕ, HasUnitDistanceConfiguration n → n ≤ 7) ↔
      ¬ HasUnitDistanceConfiguration 8 := by
  constructor
  · intro h h8
    have := h 8 h8
    omega
  · intro h8 n hn
    by_contra h
    apply h8
    exact configuration_mono (by omega) hn

theorem greatest_iff_seven_and_no_eight :
    IsGreatest {n : ℕ | HasUnitDistanceConfiguration n} 7 ↔
      HasUnitDistanceConfiguration 7 ∧ ¬ HasUnitDistanceConfiguration 8 := by
  rw [greatest_iff_expanded, upper_bound_iff_no_eight]

/-- The three-term arithmetic endpoint of the closed-polygon majority argument. -/
theorem three_term_majority_positive {a b c : ℝ}
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (ha_lt : a < b + c) :
    0 < -a + b + c := by
  linarith

/-- The four-term arithmetic endpoint of the closed-polygon majority argument. -/
theorem four_term_majority_positive {a b c d : ℝ}
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d)
    (hd_lt : d < a + b + c) :
    0 < a + b + c - d := by
  linarith

/-- The inline Formal Conjectures statement has the same meaning as the helper predicate. -/
theorem inline_statement_iff_helper :
    (IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7) ↔ IsGreatest {n : ℕ | HasUnitDistanceConfiguration n} 7 := by
  have hs :
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1} =
      {n : ℕ | HasUnitDistanceConfiguration n} := by
    ext n
    constructor
    · rintro ⟨L, hdim, hdist⟩
      exact ⟨fun i => ⟨L i, hdim i⟩, fun i j hij => hdist i j hij⟩
    · rintro ⟨L, hL⟩
      exact ⟨fun i => (L i).1, fun i => (L i).2, fun i j hij => hL hij⟩
  rw [hs]

theorem seven_exists : HasUnitDistanceConfiguration 7 := by
  obtain ⟨L, hdim, hdist⟩ := LowerCertificate.exists_seven_affine_lines
  exact ⟨fun i => ⟨L i, hdim i⟩, fun i j hij => hdist i j hij⟩

/-- The geometric reduction includes parallel and dependent directions and
produces the sign system used by the upper-bound proof. -/
theorem eight_implies_sign_system (h8 : HasUnitDistanceConfiguration 8) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ Upper.SignRealizable E χ := by
  obtain ⟨L, hL⟩ := h8
  exact Upper.signs_of_affine_configuration (fun i => (L i).1) (fun i => (L i).2)
    (fun i j hij => hL hij)

/-- The finite proof uses this normalization and these necessary clauses. -/
theorem eight_implies_normalized_sign_checks (h8 : HasUnitDistanceConfiguration 8) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧
      (∀ i, i ≠ 0 → E 0 i = 1) ∧ χ 0 1 2 = 1 ∧
      Upper.SignRealizable E χ ∧ Upper.NecessarySignChecks E χ := by
  obtain ⟨L, hL⟩ := h8
  exact Upper.normalized_sign_system_of_affine_configuration
    (fun i => (L i).1) (fun i => (L i).2) (fun i j hij => hL hij)

/-- The 131 contact matrices cover every hypothetical eight-axis configuration. -/
theorem eight_implies_131_cases (h8 : HasUnitDistanceConfiguration 8) :
    ∃ k : Fin Upper.GraphCover.contactReps131.size,
      ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
        (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ χ 0 1 2 = 1 ∧
        Upper.SignRealizable
          (Upper.GraphCover.contactOfGraph
            (Upper.GraphCover.maskGraph 7 Upper.GraphCover.contactReps131[k])) χ ∧
        Upper.NecessarySignChecks
          (Upper.GraphCover.contactOfGraph
            (Upper.GraphCover.maskGraph 7 Upper.GraphCover.contactReps131[k])) χ := by
  obtain ⟨L, hL⟩ := h8
  exact Upper.eight_axes_reduce_to_131
    (fun i => (L i).1) (fun i => (L i).2) (fun i j hij => hL hij)

theorem no_eight : ¬ HasUnitDistanceConfiguration 8 := by
  intro h8
  obtain ⟨k, χ, hu, hfirst, hr, hn⟩ := eight_implies_131_cases h8
  exact Upper.all_contact_representatives_excluded k χ hu hfirst hr hn

theorem maximum_seven_of
    (h7 : HasUnitDistanceConfiguration 7)
    (h8 : ¬ HasUnitDistanceConfiguration 8) :
    IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7 := by
  rw [inline_statement_iff_helper, greatest_iff_seven_and_no_eight]
  exact ⟨h7, h8⟩

/-- The affirmative Formal Conjectures target, with the geometry fully inlined. -/
theorem littlewood_cylinders : answer(True) ↔
    IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7 := by
  constructor
  · intro _
    exact maximum_seven_of seven_exists no_eight
  · intro _
    trivial

#print axioms inline_statement_iff_helper
#print axioms greatest_iff_seven_and_no_eight
#print axioms three_term_majority_positive
#print axioms four_term_majority_positive
#print axioms seven_exists
#print axioms eight_implies_sign_system
#print axioms eight_implies_normalized_sign_checks
#print axioms eight_implies_131_cases
#print axioms no_eight
#print axioms littlewood_cylinders

end LittlewoodCylinders
