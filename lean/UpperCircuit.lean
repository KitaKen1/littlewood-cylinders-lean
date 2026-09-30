import UpperCross
import UpperPolygon

namespace LittlewoodCylinders.Upper

open Finset

/-- Alternating maximal minors of a four-direction matrix. -/
noncomputable def cofactors (u : Fin 4 → Space) : Fin 4 → ℝ :=
  ![triple (u 1) (u 2) (u 3), -triple (u 0) (u 2) (u 3),
    triple (u 0) (u 1) (u 3), -triple (u 0) (u 1) (u 2)]

theorem cofactors_sum (u : Fin 4 → Space) : ∑ i, cofactors u i • u i = 0 := by
  simpa [cofactors, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using
    cofactor_relation (u 0) (u 1) (u 2) (u 3)

/-- From a four-circuit, delete an edge and at most one zero projection.
At least two different projected edges remain. -/
theorem four_indices_avoid_two (k t : Fin 4) :
    ∃ a b : Fin 4, a ≠ k ∧ b ≠ k ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t := by
  revert k t
  decide +kernel

variable {ι : Type*} [DecidableEq ι]

theorem projected_circuit_strict (u : ι → Space)
    (hdet : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0)
    (I : Fin 4 → ι) (hI : Function.Injective I) (c : Fin 4 → ℝ)
    (hc : ∑ i, c i • u (I i) = 0) (hcnz : ∀ i, c i ≠ 0) (j : ι) :
    ∀ k, 2 * ‖c k • cross (u j) (u (I k))‖ <
      ∑ i, ‖c i • cross (u j) (u (I i))‖ := by
  apply closed_polygon_strict
  · have hh := congrArg (cross (u j)) hc
    simpa [Fin.sum_univ_succ, cross_add_right, cross_smul_right] using hh
  · intro k
    have hp : ∃ a b : Fin 4, a ≠ k ∧ b ≠ k ∧ a ≠ b ∧ I a ≠ j ∧ I b ≠ j := by
      by_cases h : ∃ t, I t = j
      · obtain ⟨t, rfl⟩ := h
        obtain ⟨a, b, hak, hbk, hab, hat, hbt⟩ := four_indices_avoid_two k t
        exact ⟨a, b, hak, hbk, hab, fun heq => hat (hI heq), fun heq => hbt (hI heq)⟩
      · obtain ⟨a, b, hak, hbk, hab, _, _⟩ := four_indices_avoid_two k k
        exact ⟨a, b, hak, hbk, hab, fun heq => h ⟨a, heq⟩, fun heq => h ⟨b, heq⟩⟩
    obtain ⟨a, b, hak, hbk, hab, haj, hbj⟩ := hp
    refine ⟨a, b, hak, hbk, hab, ?_⟩
    exact projected_edges_not_collinear (u j) (u (I a)) (u (I b)) (c a) (c b)
      (hcnz a) (hcnz b) (hdet j (I a) (I b) haj.symm hbj.symm
        (fun heq => hab (hI heq)))

/-- A sign certificate for two four-circuits excludes an actual geometric
moment system. The signed contact magnitude is the unit axis-distance condition.
The finite checker only selects signs; every norm inequality is proved above. -/
theorem polygon_obstruction (u m : ι → Space)
    (hdet : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0)
    (I J : Fin 4 → ι) (hI : Function.Injective I) (c d : Fin 4 → ℝ)
    (hc : ∑ i, c i • u (I i) = 0) (hd : ∑ j, d j • u (J j) = 0)
    (hcnz : ∀ i, c i ≠ 0) (hdnz : ∀ j, d j ≠ 0)
    (hcontact : ∀ a b, |contact u m a b| = ‖cross (u a) (u b)‖)
    (g : ℝ) (hg : |g| = 1) (s : Fin 4 → Fin 4 → Bool)
    (hcheck : ∀ j, majorityCheck (s j) = true)
    (hsign : ∀ j i, if s j i then 0 ≤ g * d j * c i * contact u m (J j) (I i)
      else g * d j * c i * contact u m (J j) (I i) ≤ 0) : False := by
  let r (j i : Fin 4) := g * d j * c i * contact u m (J j) (I i)
  have habs (j i : Fin 4) : |r j i| = |d j| * ‖c i • cross (u (J j)) (u (I i))‖ := by
    simp only [r, abs_mul, hg, one_mul, hcontact, norm_smul, Real.norm_eq_abs]
    ring
  have hrows (j : Fin 4) : 0 < ∑ i, r j i := by
    have hpoly := projected_circuit_strict u hdet I hI c hc hcnz (J j)
    have hdp : 0 < |d j| := abs_pos.mpr (hdnz j)
    have hp : ∀ k, 2 * |r j k| < ∑ i, |r j i| := by
      intro k
      simp_rw [habs, ← mul_sum]
      nlinarith [mul_lt_mul_of_pos_left (hpoly k) hdp]
    have htotal : 0 < ∑ i, |r j i| := by
      have hh := hp 0
      have hn := abs_nonneg (r j 0)
      linarith
    have hmaj := majorityCheck_sound (s j) (fun i => |r j i|) (hcheck j) htotal hp
    have heq (i : Fin 4) : (if s j i then |r j i| else -|r j i|) = r j i := by
      have hh := hsign j i
      change (if s j i then 0 ≤ r j i else r j i ≤ 0) at hh
      cases hsi : s j i
      · simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hh ⊢
        rw [abs_of_nonpos hh, neg_neg]
      · simp only [hsi, ↓reduceIte] at hh ⊢
        exact abs_of_nonneg hh
    simpa only [heq] using hmaj
  have hz := moment_bilinear_zero (fun i => u (I i)) (fun i => m (I i))
    (fun j => u (J j)) (fun j => m (J j)) c d hc hd
  have heq : ∑ j, ∑ i, r j i = g *
      (∑ j, d j * (∑ i, c i * contact u m (J j) (I i))) := by
    simp only [r, mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  have hp := sum_pos (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hrows j) univ_nonempty
  rw [heq] at hp
  simp only [contact] at hp
  rw [hz, mul_zero] at hp
  exact (lt_irrefl 0) hp

#print axioms projected_circuit_strict
#print axioms polygon_obstruction

end LittlewoodCylinders.Upper
