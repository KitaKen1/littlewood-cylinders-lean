import UpperPrunedGraphCover
import UpperFiveParity
import UpperSignNormalization
import Mathlib.Data.Finset.Sort

namespace LittlewoodCylinders.Upper
open GraphCover

theorem matrixCliqueFree_of_checks
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1)
    (hn : NecessarySignChecks E χ) : MatrixCliqueFree E := by
  classical
  intro I hI f hf g hg he
  let S := Finset.univ.image I
  have hS : S.card = 5 := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hI
  let J := S.orderEmbOfFin hS
  have hJ (i : Fin 5) : ∃ j, I j = J i := by
    have hi := S.orderEmbOfFin_mem hS i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  choose p hp using hJ
  apply FiveParitySigned.signed_five_impossible E χ J (f ∘ p) g hχ J.strictMono
    (fun i => hf (p i)) hg _ hn.2
  intro i j hij
  have hpij : p i ≠ p j := by
    intro h
    apply hij
    apply J.injective
    rw [← hp i, ← hp j, h]
  simpa only [Function.comp_apply, hp] using he (p i) (p j) hpij

theorem matrixCliqueFree_of_realizable
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hd : ∀ i, E i i = 0) (hs : ∀ i j, E i j = E j i)
    (hu : ∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1)
    (hr : SignRealizable E χ) : MatrixCliqueFree E := by
  have habs (i j : Fin 8) (hij : i ≠ j) : |E i j| = 1 := by
    rcases hu i j hij with h | h <;> rw [h] <;> norm_num
  exact matrixCliqueFree_of_checks E χ hχ
    (necessarySignChecks_of_realizable E χ hd hs habs (fun a b c _ _ => hχ a b c) hr)

#print axioms matrixCliqueFree_of_realizable
end LittlewoodCylinders.Upper
