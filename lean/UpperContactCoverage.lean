import UpperPrunedSwitchingData
import UpperPrunedGraphSwitching

/-! Complete coverage by the 131 contact-matrix representatives.
The graph cover prunes signed-five obstructions with a proved hereditary invariant.
Its remaining extensions and signed permutations are kernel-checked.
The switching cover is checked entry by entry. Orientation enumeration is
a separate remaining obligation and is not assumed here. -/

namespace LittlewoodCylinders.Upper

open GraphCover

theorem normalized_system_has_contact_representative
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hd : ∀ i, E i i = 0) (hs : ∀ i j, E i j = E j i)
    (hu : ∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1)
    (hrow : ∀ i, i ≠ 0 → E 0 i = 1) (hr : SignRealizable E χ) :
    ∃ k : Fin contactReps131.size, ∃ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ a b c, ψ a b c = 1 ∨ ψ a b c = -1) ∧ ψ 0 1 2 = 1 ∧
      SignRealizable (contactOfGraph (maskGraph 7 contactReps131[k])) ψ ∧
      NecessarySignChecks (contactOfGraph (maskGraph 7 contactReps131[k])) ψ := by
  obtain ⟨k, p, hp⟩ := normalized_matrix_covered_free prunedGraphReps7 prunedGraphReps7_cover E hd hs hu hrow
    (matrixCliqueFree_of_realizable E χ hd hs hu hχ hr)
  let ψ := fun a b c => alternatingSign χ (p a) (p b) (p c)
  have hψ : ∀ a b c, ψ a b c = 1 ∨ ψ a b c = -1 :=
    fun a b c => alternatingSign_unit_all χ hχ (p a) (p b) (p c)
  have hrk : SignRealizable (contactOfGraph (maskGraph 7 prunedGraphReps7[k])) ψ := by
    have hh := signRealizable_reorient_relabel E χ hr p (fun _ => 1) (fun _ => Or.inl rfl)
    have heq : contactOfGraph (maskGraph 7 prunedGraphReps7[k]) = fun i j => E (p i) (p j) :=
      funext fun i => funext fun j => hp i j
    rw [heq]
    simpa only [one_mul] using hh
  obtain ⟨j, θ, hθ, hrj⟩ := switchValid_realizable prunedGraphReps7 contactReps131 prunedContactSwitches
    prunedContactSwitches_valid k ψ hψ hrk
  obtain ⟨hjd, hjs, hju, _⟩ := contactReps131_properties j
  have hjabs (a b : Fin 8) (hab : a ≠ b) :
      |contactOfGraph (maskGraph 7 contactReps131[j]) a b| = 1 := by
    rcases hju a b hab with hh | hh <;> rw [hh] <;> norm_num
  rcases hθ 0 1 2 with hfirst | hfirst
  · exact ⟨j, θ, hθ, hfirst, hrj,
      necessarySignChecks_of_realizable _ θ hjd hjs hjabs (fun a b c _ _ => hθ a b c) hrj⟩
  · let θ' := fun a b c => -θ a b c
    have hr' : SignRealizable (contactOfGraph (maskGraph 7 contactReps131[j])) θ' :=
      signRealizable_neg_orientation _ θ hrj
    have hθ' (a b c : Fin 8) : θ' a b c = 1 ∨ θ' a b c = -1 := by
      rcases hθ a b c with hh | hh <;> simp [θ', hh]
    refine ⟨j, θ', hθ', ?_, hr', ?_⟩
    · simp [θ', hfirst]
    · exact necessarySignChecks_of_realizable _ θ' hjd hjs hjabs
        (fun a b c _ _ => hθ' a b c) hr'

/-- An arbitrary hypothetical configuration of eight unit-distance affine
axes has one of the 131 stored contact matrices, with an orientation table
that satisfies the proved necessary sign conditions. -/
theorem eight_axes_reduce_to_131
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1) :
    ∃ k : Fin contactReps131.size, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧ χ 0 1 2 = 1 ∧
      SignRealizable (contactOfGraph (maskGraph 7 contactReps131[k])) χ ∧
      NecessarySignChecks (contactOfGraph (maskGraph 7 contactReps131[k])) χ := by
  obtain ⟨E, χ, hd, hs, hu, hχ, hrow, _, hr, _⟩ :=
    normalized_sign_system_of_affine_configuration L hdim hdist
  exact normalized_system_has_contact_representative E χ hd hs hu hχ hrow hr

#print axioms eight_axes_reduce_to_131

end LittlewoodCylinders.Upper
