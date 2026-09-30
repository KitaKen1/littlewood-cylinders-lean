import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A small certificate interface for exhaustive graph classification.
Coverage grows by adding one vertex. Only extensions of already covered
representatives must be checked; no graph-atlas completeness is assumed. -/

namespace LittlewoodCylinders.Upper.GraphCover

abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

def Valid {n : ℕ} (G : Graph n) : Prop :=
  (∀ i, G i i = false) ∧ ∀ i j, G i j = G j i

def Iso {n : ℕ} (G H : Graph n) : Prop :=
  ∃ p : Equiv.Perm (Fin n), ∀ i j, G i j = H (p i) (p j)

theorem iso_trans {n : ℕ} {G H K : Graph n} (hGH : Iso G H) (hHK : Iso H K) : Iso G K := by
  obtain ⟨p, hp⟩ := hGH
  obtain ⟨q, hq⟩ := hHK
  exact ⟨p.trans q, fun i j => (hp i j).trans (hq (p i) (p j))⟩

def extend {n : ℕ} (G : Graph n) (b : Fin n → Bool) : Graph (n + 1) :=
  Fin.cases (Fin.cases false b) (fun i => Fin.cases (b i) (G i))

def liftPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun i => (p i).succ)
  invFun := Fin.cases 0 (fun i => (p.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem liftPerm_zero {n : ℕ} (p : Equiv.Perm (Fin n)) : liftPerm p 0 = 0 := rfl
@[simp] theorem liftPerm_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPerm p i.succ = (p i).succ := rfl

theorem iso_extension_of_tail {n : ℕ} (G : Graph (n + 1)) (H : Graph n)
    (hG : Valid G) (h : Iso (fun i j => G i.succ j.succ) H) :
    ∃ b : Fin n → Bool, Iso G (extend H b) := by
  obtain ⟨p, hp⟩ := h
  let b := fun i => G 0 (p.symm i).succ
  refine ⟨b, liftPerm p, ?_⟩
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa [extend] using hG.1 0
  · simp [extend, b]
  · simpa [extend, b] using hG.2 i.succ 0
  · simpa [extend] using hp i j

def maskGraph (n m : ℕ) : Graph n := fun i j => m.testBit (n * i.val + j.val)

def Covers {n : ℕ} (reps : Array ℕ) : Prop :=
  ∀ G : Graph n, Valid G → ∃ k : Fin reps.size, Iso G (maskGraph n reps[k])

theorem covers_zero : Covers (n := 0) #[0] := by
  intro G _
  refine ⟨0, Equiv.refl _, ?_⟩
  intro i
  exact Fin.elim0 i

theorem covers_succ {n : ℕ} (parents children : Array ℕ)
    (hprev : Covers (n := n) parents)
    (hstep : ∀ k : Fin parents.size, ∀ b : Fin n → Bool,
      ∃ j : Fin children.size, Iso (extend (maskGraph n parents[k]) b)
        (maskGraph (n + 1) children[j])) : Covers (n := n + 1) children := by
  intro G hG
  have htail : Valid (fun i j : Fin n => G i.succ j.succ) :=
    ⟨fun i => hG.1 i.succ, fun i j => hG.2 i.succ j.succ⟩
  obtain ⟨k, hk⟩ := hprev _ htail
  obtain ⟨b, hb⟩ := iso_extension_of_tail G _ hG hk
  obtain ⟨j, hj⟩ := hstep k b
  exact ⟨j, iso_trans hb hj⟩

def boolCode {n : ℕ} (b : Fin n → Bool) : ℕ :=
  ∑ i, if b i then 2 ^ i.val else 0

/-- Base-eight digits specify a permutation, whose bijectivity is checked.
Out-of-range digits are harmless: only the decoded map is ever used. -/
def decodePerm (n code : ℕ) : Fin n → Fin n :=
  fun i => ⟨(code / 8 ^ i.val % 8) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A witness stores the child index, permutation and redundant child mask.
The mask equality is checked once before the edge comparisons. -/
def RowValid (n parent : ℕ) (children : Array ℕ) (row : Array (ℕ × ℕ × ℕ)) : Prop :=
  ∀ b : Fin n → Bool,
    let w := row.getD (boolCode b) (0, 0, 0)
    w.1 < children.size ∧ children.getD w.1 0 = w.2.2 ∧
    Function.Bijective (decodePerm (n + 1) w.2.1) ∧
    ∀ i j, extend (maskGraph n parent) b i j =
      maskGraph (n + 1) w.2.2
        (decodePerm (n + 1) w.2.1 i) (decodePerm (n + 1) w.2.1 j)

instance (n parent : ℕ) (children : Array ℕ) (row : Array (ℕ × ℕ × ℕ)) :
    Decidable (RowValid n parent children row) := inferInstanceAs (Decidable (∀ _, _))

def StepValid (n : ℕ) (parents children : Array ℕ)
    (cert : Array (Array (ℕ × ℕ × ℕ))) : Prop :=
  ∀ k : Fin parents.size, RowValid n parents[k] children (cert.getD k.val #[])

instance (n : ℕ) (parents children : Array ℕ) (cert : Array (Array (ℕ × ℕ × ℕ))) :
    Decidable (StepValid n parents children cert) := inferInstanceAs (Decidable (∀ _, _))

theorem stepValid_covers {n : ℕ} (parents children : Array ℕ) (cert : Array (Array (ℕ × ℕ × ℕ)))
    (hprev : Covers (n := n) parents) (hcert : StepValid n parents children cert) :
    Covers (n := n + 1) children := by
  apply covers_succ parents children hprev
  intro k b
  obtain ⟨hj, hm, hp, heq⟩ := hcert k b
  refine ⟨⟨_, hj⟩, Equiv.ofBijective _ hp, ?_⟩
  intro i j
  rw [← hm] at heq
  simpa only [Equiv.ofBijective_apply, Fin.getElem_fin,
    ← Array.getElem_eq_getD (xs := children) (h := hj) 0] using heq i j

#print axioms stepValid_covers

end LittlewoodCylinders.Upper.GraphCover
