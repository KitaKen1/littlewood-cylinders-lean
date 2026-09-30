import UpperNormObstructions
import UpperMoment

namespace LittlewoodCylinders.Upper

open Finset

section Geometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [DecidableEq ι]

/-- One noncollinear pair suffices to make the finite triangle inequality strict. -/
theorem norm_sum_lt_of_pair (v : ι → V) (s : Finset ι) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j)
    (hstrict : ‖v j‖ • v i ≠ ‖v i‖ • v j) :
    ‖∑ k ∈ s, v k‖ < ∑ k ∈ s, ‖v k‖ := by
  have hj' : j ∈ s.erase i := mem_erase.mpr ⟨hne.symm, hj⟩
  have hv : ∑ k ∈ s, v k = v i + v j + ∑ k ∈ (s.erase i).erase j, v k := by
    rw [← add_sum_erase s v hi, ← add_sum_erase (s.erase i) v hj']
    abel
  have hn : ∑ k ∈ s, ‖v k‖ = ‖v i‖ + ‖v j‖ +
      ∑ k ∈ (s.erase i).erase j, ‖v k‖ := by
    rw [← add_sum_erase s (fun k => ‖v k‖) hi,
      ← add_sum_erase (s.erase i) (fun k => ‖v k‖) hj']
    ring
  rw [hv, hn]
  have h₁ := norm_add_le (v i + v j) (∑ k ∈ (s.erase i).erase j, v k)
  have h₂ := norm_sum_le ((s.erase i).erase j) v
  have h₃ := strict_triangle hstrict
  linarith

/-- Closed polygons have a strict edge-versus-complement inequality whenever
the complementary edges include a noncollinear pair. -/
theorem closed_polygon_strict [Fintype ι] (v : ι → V)
    (hclosed : ∑ i, v i = 0)
    (hpairs : ∀ k, ∃ i j, i ≠ k ∧ j ≠ k ∧ i ≠ j ∧
      ‖v j‖ • v i ≠ ‖v i‖ • v j) :
    ∀ k, 2 * ‖v k‖ < ∑ i, ‖v i‖ := by
  intro k
  obtain ⟨i, j, hik, hjk, hij, hstrict⟩ := hpairs k
  have hlt := norm_sum_lt_of_pair v (univ.erase k)
    (by simp [hik]) (by simp [hjk]) hij hstrict
  have hsum : ∑ i ∈ univ.erase k, v i = -v k := by
    have h := add_sum_erase univ v (mem_univ k)
    rw [hclosed] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [hsum, norm_neg] at hlt
  have hnorm := add_sum_erase univ (fun i => ‖v i‖) (mem_univ k)
  linarith

end Geometry

/-- A four-entry sign row has at most one negative entry. Zero entries may
be marked positive. This six-bit test is the certificate checker. -/
def majorityCheck (s : Fin 4 → Bool) : Bool :=
  (s 0 || s 1) && (s 0 || s 2) && (s 0 || s 3) &&
  (s 1 || s 2) && (s 1 || s 3) && (s 2 || s 3)

/-- Soundness of the finite sign checker, with strict polygon inequalities. -/
theorem majorityCheck_sound (s : Fin 4 → Bool) (a : Fin 4 → ℝ)
    (hcheck : majorityCheck s = true)
    (hpos : 0 < ∑ i, a i) (hpoly : ∀ k, 2 * a k < ∑ i, a i) :
    0 < ∑ i, if s i then a i else -a i := by
  have h₀ := hpoly 0
  have h₁ := hpoly 1
  have h₂ := hpoly 2
  have h₃ := hpoly 3
  simp [Fin.sum_univ_succ] at hpos h₀ h₁ h₂ h₃
  cases hs₀ : s 0 <;> cases hs₁ : s 1 <;>
    cases hs₂ : s 2 <;> cases hs₃ : s 3 <;>
    simp_all [majorityCheck, Fin.sum_univ_succ] <;>
    linarith [hpoly 0, hpoly 1, hpoly 2, hpoly 3]

#print axioms closed_polygon_strict
#print axioms majorityCheck_sound

end LittlewoodCylinders.Upper
