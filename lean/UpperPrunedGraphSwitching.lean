import UpperGraphSwitching
import UpperCliqueFree

namespace LittlewoodCylinders.Upper.GraphCover

theorem normalized_matrix_covered_free (reps : Array ℕ) (hcover : CoversFree (n := 7) reps)
    (E : Fin 8 → Fin 8 → ℤ)
    (hd : ∀ i, E i i = 0) (hs : ∀ i j, E i j = E j i)
    (hu : ∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1)
    (hrow : ∀ i, i ≠ 0 → E 0 i = 1) (hfree : MatrixCliqueFree E) :
    ∃ k : Fin reps.size, ∃ p : Equiv.Perm (Fin 8),
      ∀ i j, contactOfGraph (maskGraph 7 reps[k]) i j = E (p i) (p j) := by
  let G : Graph 7 := fun i j => decide (E i.succ j.succ = -1)
  have hG : Valid G := by
    constructor
    · intro i; simp [G, hd]
    · intro i j; dsimp [G]; rw [hs i.succ j.succ]
  have hE : E = contactOfGraph G := by
    funext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [contactOfGraph, hd]
    · simp [contactOfGraph, hrow _ (Fin.succ_ne_zero _), zero_ne_succ]
    · rw [hs i.succ 0]
      simp [contactOfGraph, hrow _ (Fin.succ_ne_zero _)]
    · by_cases hij : i = j
      · subst j; simp [contactOfGraph, hd]
      · rcases hu i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) with h | h <;>
          simp [contactOfGraph, G, hij, h]
  have hfreeG : CliqueFree G := by
    change MatrixCliqueFree (contactOfGraph G)
    rw [← hE]
    exact hfree
  obtain ⟨k, p, hp⟩ := hcover G hG hfreeG
  refine ⟨k, (liftPerm p).symm, ?_⟩
  intro i j
  rw [hE]
  simpa only [Equiv.apply_symm_apply] using
    (contactOfGraph_relabel G _ p hp ((liftPerm p).symm i) ((liftPerm p).symm j)).symm

#print axioms normalized_matrix_covered_free
end LittlewoodCylinders.Upper.GraphCover
