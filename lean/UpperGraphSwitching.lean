import UpperGraphSwitchingCheck
import UpperSignNormalization

/-! Convert normalized sign matrices to graphs, and check explicit switching
witnesses. This interface never assumes that a list of representatives is complete. -/

namespace LittlewoodCylinders.Upper.GraphCover

theorem normalized_matrix_covered (reps : Array ℕ) (hcover : Covers (n := 7) reps)
    (E : Fin 8 → Fin 8 → ℤ)
    (hd : ∀ i, E i i = 0) (hs : ∀ i j, E i j = E j i)
    (hu : ∀ i j, i ≠ j → E i j = 1 ∨ E i j = -1)
    (hrow : ∀ i, i ≠ 0 → E 0 i = 1) :
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
  obtain ⟨k, p, hp⟩ := hcover G hG
  refine ⟨k, (liftPerm p).symm, ?_⟩
  intro i j
  rw [hE]
  simpa only [Equiv.apply_symm_apply] using
    (contactOfGraph_relabel G _ p hp ((liftPerm p).symm i) ((liftPerm p).symm j)).symm

theorem signed_relabel_realizable (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (hr : SignRealizable E χ)
    (p : Equiv.Perm (Fin 8)) (f : Fin 8 → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1)
    (g : ℤ) (hg : g = 1 ∨ g = -1) :
    SignRealizable (fun i j => g * f i * f j * E (p i) (p j))
      (fun a b c => f a * f b * f c * alternatingSign χ (p a) (p b) (p c)) := by
  have hh := signRealizable_reorient_relabel E χ hr p f hf
  rcases hg with rfl | rfl
  · simpa only [one_mul] using hh
  · simpa only [neg_one_mul, neg_mul, one_mul] using signRealizable_neg_contact _ _ hh

theorem switchValid_realizable (sources targets : Array ℕ) (cert : Array SwitchWitness)
    (hcert : SwitchValid sources targets cert) (k : Fin sources.size)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1)
    (hr : SignRealizable (contactOfGraph (maskGraph 7 sources[k])) χ) :
    ∃ j : Fin targets.size, ∃ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ,
      (∀ a b c, ψ a b c = 1 ∨ ψ a b c = -1) ∧
      SignRealizable (contactOfGraph (maskGraph 7 targets[j])) ψ := by
  let w := cert.getD k.val default
  obtain ⟨hj, hp, heq⟩ := hcert k
  let p := Equiv.ofBijective (decodePerm 8 w.permCode) hp
  have hf (i : Fin 8) : w.flips i = 1 ∨ w.flips i = -1 := by
    unfold SwitchWitness.flips
    split <;> simp
  have hg : w.sign = 1 ∨ w.sign = -1 := by
    unfold SwitchWitness.sign
    split <;> simp
  have hr' := signed_relabel_realizable _ χ hr p w.flips hf w.sign hg
  refine ⟨⟨w.target, hj⟩,
    (fun a b c => w.flips a * w.flips b * w.flips c * alternatingSign χ (p a) (p b) (p c)), ?_, ?_⟩
  · intro a b c
    exact mul_sign_unit (mul_sign_unit (mul_sign_unit (hf a) (hf b)) (hf c))
      (alternatingSign_unit_all χ hχ (p a) (p b) (p c))
  · have hmatrix : contactOfGraph (maskGraph 7 targets[(⟨w.target, hj⟩ : Fin targets.size)]) =
        fun i j => w.sign * w.flips i * w.flips j *
          contactOfGraph (maskGraph 7 sources[k]) (p i) (p j) := by
      funext i j
      simpa only [p, Equiv.ofBijective_apply, Fin.getElem_fin,
        ← Array.getElem_eq_getD (xs := targets) (h := hj) 0] using heq i j
    rw [hmatrix]
    exact hr'

#print axioms normalized_matrix_covered
#print axioms switchValid_realizable

end LittlewoodCylinders.Upper.GraphCover
