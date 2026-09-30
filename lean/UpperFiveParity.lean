import UpperTetrahedron

namespace LittlewoodCylinders.Upper.FiveParitySigned
set_option maxHeartbeats 0

theorem four_sign_product (g : ℤ) (hg : g = 1 ∨ g = -1)
    (s : Fin 4 → ℤ) (hu : ∀ i, s i = 1 ∨ s i = -1)
    (h : tetraCountCheck (tetraEdgeBits (fun j i => g * s j * s i)) = true) :
    s 0 * s 1 * s 2 * s 3 = -1 := by
  rcases hg with hg | hg <;> rcases hu 0 with h0 | h0 <;>
    rcases hu 1 with h1 | h1 <;> rcases hu 2 with h2 | h2 <;>
    rcases hu 3 with h3 | h3
  all_goals norm_num [h0, h1, h2, h3]
  all_goals
    have hf : tetraCountCheck (tetraEdgeBits (fun j i => g * s j * s i)) = false := by
      simp only [tetraEdgeBits, hg, h0, h1, h2, h3]
      decide +kernel
    simp [hf] at h

theorem four_product (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8)
    (f : Fin 4 → ℤ) (g : ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hI : StrictMono I)
    (hf : ∀ i, f i = 1 ∨ f i = -1) (hg : g = 1 ∨ g = -1)
    (he : ∀ i j, i ≠ j → E (I i) (I j) = g * f i * f j)
    (h : tetraCountCheck (tetraEdgeBits (tetraMatrix E χ I)) = true) :
    (f 0 * f 1 * f 2 * f 3) *
      (χ (I 0) (I 1) (I 2) * χ (I 0) (I 1) (I 3) *
        χ (I 0) (I 2) (I 3) * χ (I 1) (I 2) (I 3)) = -1 := by
  have hu' := signedMinors_unit χ (fun a b c _ _ => hu a b c) I hI
  have hs (i : Fin 4) : f i * signedMinors χ I i = 1 ∨ f i * signedMinors χ I i = -1 := by
    rcases hf i with hf | hf <;> rcases hu' i with hs | hs <;> simp [hf, hs]
  have hb (i j : Fin 4) (hij : i ≠ j) : tetraMatrix E χ I i j =
      g * (f i * signedMinors χ I i) * (f j * signedMinors χ I j) := by
    simp only [tetraMatrix, he i j hij]
    ring
  have hh : tetraCountCheck
      (tetraEdgeBits (fun j i => g * (f j * signedMinors χ I j) * (f i * signedMinors χ I i))) = true := by
    simpa only [tetraEdgeBits, hb 0 1 (by decide), hb 0 2 (by decide),
      hb 0 3 (by decide), hb 1 2 (by decide), hb 1 3 (by decide), hb 2 3 (by decide)] using h
  have hp := four_sign_product g hg (fun i => f i * signedMinors χ I i) hs hh
  convert hp using 1
  dsimp [signedMinors]
  ring

/-- A switched all-positive or all-negative five-clique is already forbidden
by the tetrahedron conditions. Each vertex sign occurs four times, and each
triple sign twice, in the product of the five face equations. -/
theorem signed_five_impossible (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 5 → Fin 8)
    (f : Fin 5 → ℤ) (g : ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hI : StrictMono I)
    (hf : ∀ i, f i = 1 ∨ f i = -1) (hg : g = 1 ∨ g = -1)
    (he : ∀ i j, i ≠ j → E (I i) (I j) = g * f i * f j)
    (hc : ∀ J : Fin 4 → Fin 8, StrictMono J →
      tetraCountCheck (tetraEdgeBits (tetraMatrix E χ J)) = true) : False := by
  have face (J : Fin 4 → Fin 5) (hJ : StrictMono J) :
      (f (J 0) * f (J 1) * f (J 2) * f (J 3)) *
        (χ (I (J 0)) (I (J 1)) (I (J 2)) * χ (I (J 0)) (I (J 1)) (I (J 3)) *
          χ (I (J 0)) (I (J 2)) (I (J 3)) * χ (I (J 1)) (I (J 2)) (I (J 3))) = -1 :=
    four_product E χ (I ∘ J) (f ∘ J) g hu (hI.comp hJ) (fun i => hf (J i)) hg
      (fun i j hij => he _ _ (fun h => hij (hJ.injective h))) (hc _ (hI.comp hJ))

  have h0 := face ![0, 1, 2, 3] (by decide)
  have h1 := face ![0, 1, 2, 4] (by decide)
  have h2 := face ![0, 1, 3, 4] (by decide)
  have h3 := face ![0, 2, 3, 4] (by decide)
  have h4 := face ![1, 2, 3, 4] (by decide)
  dsimp at h0 h1 h2 h3 h4
  have hs (a b c : Fin 8) : (χ a b c) ^ 2 = 1 := by
    rcases hu a b c with h | h <;> rw [h] <;> norm_num
  have hf4 (i : Fin 5) : (f i) ^ 4 = 1 := by
    rcases hf i with h | h <;> rw [h] <;> norm_num
  have hp :
      ((f 0 * f 1 * f 2 * f 3) * (χ (I 0) (I 1) (I 2) * χ (I 0) (I 1) (I 3) * χ (I 0) (I 2) (I 3) * χ (I 1) (I 2) (I 3))) *
      ((f 0 * f 1 * f 2 * f 4) * (χ (I 0) (I 1) (I 2) * χ (I 0) (I 1) (I 4) * χ (I 0) (I 2) (I 4) * χ (I 1) (I 2) (I 4))) *
      ((f 0 * f 1 * f 3 * f 4) * (χ (I 0) (I 1) (I 3) * χ (I 0) (I 1) (I 4) * χ (I 0) (I 3) (I 4) * χ (I 1) (I 3) (I 4))) *
      ((f 0 * f 2 * f 3 * f 4) * (χ (I 0) (I 2) (I 3) * χ (I 0) (I 2) (I 4) * χ (I 0) (I 3) (I 4) * χ (I 2) (I 3) (I 4))) *
      ((f 1 * f 2 * f 3 * f 4) * (χ (I 1) (I 2) (I 3) * χ (I 1) (I 2) (I 4) * χ (I 1) (I 3) (I 4) * χ (I 2) (I 3) (I 4))) =
      (f 0) ^ 4 * (f 1) ^ 4 * (f 2) ^ 4 * (f 3) ^ 4 * (f 4) ^ 4 *
      (χ (I 0) (I 1) (I 2)) ^ 2 * (χ (I 0) (I 1) (I 3)) ^ 2 * (χ (I 0) (I 1) (I 4)) ^ 2 * (χ (I 0) (I 2) (I 3)) ^ 2 * (χ (I 0) (I 2) (I 4)) ^ 2 * (χ (I 0) (I 3) (I 4)) ^ 2 * (χ (I 1) (I 2) (I 3)) ^ 2 * (χ (I 1) (I 2) (I 4)) ^ 2 * (χ (I 1) (I 3) (I 4)) ^ 2 * (χ (I 2) (I 3) (I 4)) ^ 2 := by ring
  rw [h0, h1, h2, h3, h4] at hp
  simp only [hs, hf4] at hp
  norm_num at hp

#print axioms signed_five_impossible
end LittlewoodCylinders.Upper.FiveParitySigned
