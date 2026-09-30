import UpperGraphSwitchingCheck
import Mathlib.Tactic.Ring

/- A redundant target mask avoids repeated reduction of the target array.
Only the strict upper triangle is compared; symmetry and zero diagonals
recover the other entries. All auxiliary facts are ordinary kernel proofs. -/
namespace LittlewoodCylinders.Upper.GraphCover

instance {n : ℕ} (G : Graph n) : Decidable (Valid G) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem contactOfGraph_diag {n : ℕ} (G : Graph n) (i : Fin (n + 1)) :
    contactOfGraph G i i = 0 := by simp [contactOfGraph]

theorem contactOfGraph_symm {n : ℕ} (G : Graph n) (hG : Valid G) :
    ∀ i j, contactOfGraph G i j = contactOfGraph G j i := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simp [contactOfGraph, zero_ne_succ]
  · simp [contactOfGraph, zero_ne_succ]
  · by_cases h : i = j
    · subst j; rfl
    · simp only [contactOfGraph, Fin.succ_inj, h, Ne.symm h, ↓reduceIte,
        Fin.cases_succ]
      rw [hG.2 i j]

def SwitchRowValidFast (source targetMask : ℕ) (targets : Array ℕ)
    (w : SwitchWitness) : Prop :=
  w.target < targets.size ∧ targets.getD w.target 0 = targetMask ∧
  Function.Bijective (decodePerm 8 w.permCode) ∧
  ∀ i j, i < j → contactOfGraph (maskGraph 7 targetMask) i j =
    w.sign * w.flips i * w.flips j * contactOfGraph (maskGraph 7 source)
      (decodePerm 8 w.permCode i) (decodePerm 8 w.permCode j)

instance (source targetMask : ℕ) (targets : Array ℕ) (w : SwitchWitness) :
    Decidable (SwitchRowValidFast source targetMask targets w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem switchRowValidFast_sound (source targetMask : ℕ) (targets : Array ℕ)
    (w : SwitchWitness) (hs : Valid (maskGraph 7 source))
    (ht : Valid (maskGraph 7 targetMask))
    (h : SwitchRowValidFast source targetMask targets w) :
    SwitchRowValid source targets w := by
  obtain ⟨hj, hm, hp, he⟩ := h
  refine ⟨hj, hp, ?_⟩
  rw [hm]
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact he i j hij
  · subst j; simp only [contactOfGraph_diag, mul_zero]
  · rw [contactOfGraph_symm _ ht i j, he j i hij,
      contactOfGraph_symm _ hs (decodePerm 8 w.permCode j) (decodePerm 8 w.permCode i)]
    ring

#print axioms switchRowValidFast_sound

end LittlewoodCylinders.Upper.GraphCover
