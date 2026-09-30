import UpperGrassmannPlucker
import UpperTetrahedron
import UpperSignExtraction

/-! Geometric soundness of the necessary clauses in the finite search.
The Grassmann–Plücker loop uses an anchor and four increasing other indices,
matching the Python generator and avoiding all permutations of five indices. -/

namespace LittlewoodCylinders.Upper

def NecessarySignChecks (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) : Prop :=
  (∀ a (I : Fin 4 → Fin 8), StrictMono I → (∀ i, I i ≠ a) →
    gpCheck χ a (I 0) (I 1) (I 2) (I 3) = true) ∧
  (∀ I : Fin 4 → Fin 8, StrictMono I →
    tetraCountCheck (tetraEdgeBits (tetraMatrix E χ I)) = true)

instance (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) :
    Decidable (NecessarySignChecks E χ) := inferInstanceAs (Decidable (_ ∧ _))

theorem necessarySignChecks_of_realizable (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hdiag : ∀ i, E i i = 0) (hsym : ∀ i j, E i j = E j i)
    (hE : ∀ i j, i ≠ j → |E i j| = 1)
    (hχunit : ∀ a b c, a < b → b < c → χ a b c = 1 ∨ χ a b c = -1)
    (h : SignRealizable E χ) : NecessarySignChecks E χ := by
  obtain ⟨u, m, hT, hχ⟩ := h
  constructor
  · intro a I hI ha
    have hinj : Function.Injective (Fin.cons a I : Fin 5 → Fin 8) :=
      Fin.cons_injective_iff.mpr ⟨by rintro ⟨i, hi⟩; exact ha i hi, hI.injective⟩
    have hh := gpCheck_of_sorted_signs u χ hχ (Fin.cons a I) hinj
    rw [show (1 : Fin 5) = (0 : Fin 4).succ from rfl,
      show (2 : Fin 5) = (1 : Fin 4).succ from rfl,
      show (3 : Fin 5) = (2 : Fin 4).succ from rfl,
      show (4 : Fin 5) = (3 : Fin 4).succ from rfl] at hh
    simpa only [Fin.cons_zero, Fin.cons_succ] using hh
  · intro I hI
    rw [← tetrahedronCheck_eq_count E χ I hdiag hsym hE hχunit hI]
    exact tetrahedronCheck_of_realization E χ u m hE hχunit hT hχ I hI

/-- The original affine-line hypotheses imply the necessary finite clauses.
There is no assumption about generic position, a SAT solver, or enumeration. -/
theorem affine_configuration_satisfies_sign_checks
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1) :
    ∃ E : Fin 8 → Fin 8 → ℤ, ∃ χ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ i, E i i = 0) ∧ (∀ i j, E i j = E j i) ∧
      (∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1) ∧
      (∀ a b c, χ a b c = 1 ∨ χ a b c = -1) ∧
      SignRealizable E χ ∧ NecessarySignChecks E χ := by
  obtain ⟨E, χ, hdiag, hsym, hE, hχ, hr⟩ := signs_of_affine_configuration L hdim hdist
  refine ⟨E, χ, hdiag, hsym, hE, hχ, hr, ?_⟩
  apply necessarySignChecks_of_realizable E χ hdiag hsym _ (fun a b c _ _ => hχ a b c) hr
  intro i j hij
  rcases hE i j hij with hh | hh <;> simp [hh]

#print axioms affine_configuration_satisfies_sign_checks

end LittlewoodCylinders.Upper
