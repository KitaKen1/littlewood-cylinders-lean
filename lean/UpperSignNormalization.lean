import UpperNecessarySigns
import UpperSignSymmetry

/-! Normalize the first contact row and the first determinant sign using
proved realizability symmetries. Necessary checks can then be re-derived,
so no separate invariance proof for every Boolean clause is needed. -/

namespace LittlewoodCylinders.Upper

theorem mul_sign_unit {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem alternatingSign_unit_all (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (a b c : Fin 8) :
    alternatingSign χ a b c = 1 ∨ alternatingSign χ a b c = -1 := by
  have hn (i j k : Fin 8) : -χ i j k = 1 ∨ -χ i j k = -1 := by
    rcases hχ i j k with h | h <;> simp [h]
  unfold alternatingSign
  split_ifs <;> first | exact hχ _ _ _ | exact hn _ _ _

/-- The first contact row can be made all positive, and the first orientation
sign can be made positive independently. -/
theorem exists_normalized_sign_system
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hdiag : ∀ i, E i i = 0) (hsym : ∀ i j, E i j = E j i)
    (hE : ∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hr : SignRealizable E χ) :
    ∃ A : Fin 8 → Fin 8 → ℤ, ∃ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, A i i = 0) ∧ (∀ i j, A i j = A j i) ∧
      (∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) ∧
      (∀ a b c, ψ a b c = 1 ∨ ψ a b c = -1) ∧
      (∀ i, i ≠ 0 → A 0 i = 1) ∧ ψ 0 1 2 = 1 ∧
      SignRealizable A ψ ∧ NecessarySignChecks A ψ := by
  let f := fun i : Fin 8 => if i = 0 then (1 : ℤ) else E 0 i
  have hf (i : Fin 8) : f i = 1 ∨ f i = -1 := by
    by_cases hi : i = 0
    · simp [f, hi]
    · simpa only [f, if_neg hi] using hE 0 i (Ne.symm hi)
  let A := fun i j => f i * f j * E i j
  let ψ := fun a b c => f a * f b * f c * alternatingSign χ a b c
  have hA : SignRealizable A ψ := by
    simpa only [Equiv.refl_apply] using signRealizable_reorient_relabel E χ hr (Equiv.refl _) f hf
  have hAd (i : Fin 8) : A i i = 0 := by simp [A, hdiag]
  have hAs (i j : Fin 8) : A i j = A j i := by
    dsimp [A]
    rw [hsym i j]
    ring
  have hAu (i j : Fin 8) (hij : i ≠ j) : A i j = 1 ∨ A i j = -1 :=
    mul_sign_unit (mul_sign_unit (hf i) (hf j)) (hE i j hij)
  have hψu (a b c : Fin 8) : ψ a b c = 1 ∨ ψ a b c = -1 :=
    mul_sign_unit (mul_sign_unit (mul_sign_unit (hf a) (hf b)) (hf c))
      (alternatingSign_unit_all χ hχ a b c)
  have hrow (i : Fin 8) (hi : i ≠ 0) : A 0 i = 1 := by
    rcases hE 0 i (Ne.symm hi) with hh | hh <;> simp [A, f, hi, hh]
  have hAabs (i j : Fin 8) (hij : i ≠ j) : |A i j| = 1 := by
    rcases hAu i j hij with hh | hh <;> simp [hh]
  rcases hψu 0 1 2 with hfirst | hfirst
  · exact ⟨A, ψ, hAd, hAs, hAu, hψu, hrow, hfirst, hA,
      necessarySignChecks_of_realizable A ψ hAd hAs hAabs (fun a b c _ _ => hψu a b c) hA⟩
  · let ψ' := fun a b c => -ψ a b c
    have hr' : SignRealizable A ψ' := signRealizable_neg_orientation A ψ hA
    have hu' (a b c : Fin 8) : ψ' a b c = 1 ∨ ψ' a b c = -1 := by
      rcases hψu a b c with hh | hh <;> simp [ψ', hh]
    refine ⟨A, ψ', hAd, hAs, hAu, hu', hrow, ?_, hr', ?_⟩
    · simp [ψ', hfirst]
    · exact necessarySignChecks_of_realizable A ψ' hAd hAs hAabs
        (fun a b c _ _ => hu' a b c) hr'

theorem normalized_sign_system_of_affine_configuration
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧
      (∀ i, i ≠ 0 → E 0 i = 1) ∧ χ 0 1 2 = 1 ∧
      SignRealizable E χ ∧ NecessarySignChecks E χ := by
  obtain ⟨E, χ, hd, hs, hE, hχ, hr⟩ := signs_of_affine_configuration L hdim hdist
  exact exists_normalized_sign_system E χ hd hs hE hχ hr

#print axioms normalized_sign_system_of_affine_configuration

end LittlewoodCylinders.Upper
