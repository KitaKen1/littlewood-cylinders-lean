import UpperGraphSwitchingCheck

namespace LittlewoodCylinders.Upper.GraphCover

def MatrixCliqueFree {n : ℕ} (E : Fin n → Fin n → ℤ) : Prop :=
  ∀ (I : Fin 5 → Fin n), Function.Injective I →
    ∀ (f : Fin 5 → ℤ), (∀ i, f i = 1 ∨ f i = -1) →
      ∀ g : ℤ, (g = 1 ∨ g = -1) →
        (∀ i j, i ≠ j → E (I i) (I j) = g * f i * f j) → False

def CliqueFree {n : ℕ} (G : Graph n) : Prop := MatrixCliqueFree (contactOfGraph G)

def CoversFree {n : ℕ} (reps : Array ℕ) : Prop :=
  ∀ G : Graph n, Valid G → CliqueFree G → ∃ k : Fin reps.size, Iso G (maskGraph n reps[k])

theorem matrixCliqueFree_pullback {n m : ℕ} (E : Fin n → Fin n → ℤ)
    (F : Fin m → Fin m → ℤ) (p : Fin m → Fin n) (hp : Function.Injective p)
    (he : ∀ i j, F i j = E (p i) (p j)) (h : MatrixCliqueFree E) :
    MatrixCliqueFree F := by
  intro I hI f hf g hg hE
  exact h (p ∘ I) (hp.comp hI) f hf g hg (fun i j hij => (he _ _).symm.trans (hE i j hij))

theorem cliqueFree_of_iso {n : ℕ} (G H : Graph n) (h : Iso G H)
    (hG : CliqueFree G) : CliqueFree H := by
  obtain ⟨p, hp⟩ := h
  apply matrixCliqueFree_pullback (contactOfGraph G) (contactOfGraph H)
    (liftPerm p).symm (liftPerm p).symm.injective _ hG
  intro i j
  simpa only [Equiv.apply_symm_apply] using
    (contactOfGraph_relabel G H p hp ((liftPerm p).symm i) ((liftPerm p).symm j)).symm

def skipFirstGraphVertex {n : ℕ} : Fin (n + 1) → Fin (n + 2) :=
  Fin.cases 0 (fun i => i.succ.succ)

theorem skipFirstGraphVertex_injective {n : ℕ} :
    Function.Injective (@skipFirstGraphVertex n) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · simp [skipFirstGraphVertex]
  · simp [skipFirstGraphVertex, zero_ne_succ]
  · simp [skipFirstGraphVertex]
  · simp [skipFirstGraphVertex]

theorem contactOfGraph_tail {n : ℕ} (G : Graph (n + 1)) :
    ∀ i j, contactOfGraph (fun a b => G a.succ b.succ) i j =
      contactOfGraph G (skipFirstGraphVertex i) (skipFirstGraphVertex j) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simp [contactOfGraph, skipFirstGraphVertex, zero_ne_succ]
  · simp [contactOfGraph, skipFirstGraphVertex]
  · simp only [contactOfGraph, skipFirstGraphVertex, Fin.cases_succ, Fin.succ_inj]

theorem cliqueFree_tail {n : ℕ} (G : Graph (n + 1)) (hG : CliqueFree G) :
    CliqueFree (fun i j => G i.succ j.succ) :=
  matrixCliqueFree_pullback _ _ skipFirstGraphVertex skipFirstGraphVertex_injective
    (contactOfGraph_tail G) hG

structure CliqueWitness where
  labels : ℕ
  flips : ℕ
  negative : Bool
deriving Inhabited

def CliqueWitness.index {n : ℕ} (w : CliqueWitness) (i : Fin 5) : Fin (n + 1) :=
  ⟨(w.labels / 8 ^ i.val % 8) % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

def CliqueWitness.flip (w : CliqueWitness) (i : Fin 5) : ℤ :=
  if w.flips.testBit i.val then -1 else 1

def CliqueWitness.sign (w : CliqueWitness) : ℤ := if w.negative then -1 else 1

def CliqueWitnessValid {n : ℕ} (G : Graph n) (w : CliqueWitness) : Prop :=
  Function.Injective (@CliqueWitness.index n w) ∧
  ∀ i j, i ≠ j → contactOfGraph G (w.index i) (w.index j) = w.sign * w.flip i * w.flip j

instance {n : ℕ} (G : Graph n) (w : CliqueWitness) : Decidable (CliqueWitnessValid G w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem cliqueWitnessValid_not_free {n : ℕ} (G : Graph n) (w : CliqueWitness)
    (h : CliqueWitnessValid G w) : ¬ CliqueFree G := by
  intro hG
  apply hG w.index h.1 w.flip _ w.sign _ h.2
  · intro i; unfold CliqueWitness.flip; split <;> simp
  · unfold CliqueWitness.sign; split <;> simp

inductive PrunedWitness where
  | keep (target perm mask : ℕ)
  | drop (clique : CliqueWitness)
deriving Inhabited

def PrunedEntryValid (n parent : ℕ) (children : Array ℕ)
    (b : Fin n → Bool) (w : PrunedWitness) : Prop :=
  match w with
  | .keep target perm mask =>
    target < children.size ∧ children.getD target 0 = mask ∧
    Function.Bijective (decodePerm (n + 1) perm) ∧
    ∀ i j, extend (maskGraph n parent) b i j =
      maskGraph (n + 1) mask (decodePerm (n + 1) perm i) (decodePerm (n + 1) perm j)
  | .drop w => CliqueWitnessValid (extend (maskGraph n parent) b) w

instance (n parent : ℕ) (children : Array ℕ) (b : Fin n → Bool) (w : PrunedWitness) :
    Decidable (PrunedEntryValid n parent children b w) := by
  cases w <;> unfold PrunedEntryValid <;> infer_instance

def PrunedRowValid (n parent : ℕ) (children : Array ℕ)
    (row : Array PrunedWitness) : Prop :=
  ∀ b : Fin n → Bool, PrunedEntryValid n parent children b (row.getD (boolCode b) default)

instance (n parent : ℕ) (children : Array ℕ) (row : Array PrunedWitness) :
    Decidable (PrunedRowValid n parent children row) := inferInstanceAs (Decidable (∀ _, _))

def PrunedStepValid (n : ℕ) (parents children : Array ℕ)
    (cert : Array (Array PrunedWitness)) : Prop :=
  ∀ k : Fin parents.size, PrunedRowValid n parents[k] children (cert.getD k.val #[])

theorem coversFree_zero : CoversFree (n := 0) #[0] := fun G hG _ => covers_zero G hG

theorem prunedStepValid_covers {n : ℕ} (parents children : Array ℕ)
    (cert : Array (Array PrunedWitness)) (hprev : CoversFree (n := n) parents)
    (hcert : PrunedStepValid n parents children cert) : CoversFree (n := n + 1) children := by
  intro G hG hfree
  have htail : Valid (fun i j : Fin n => G i.succ j.succ) :=
    ⟨fun i => hG.1 i.succ, fun i j => hG.2 i.succ j.succ⟩
  obtain ⟨k, hk⟩ := hprev _ htail (cliqueFree_tail G hfree)
  obtain ⟨b, hb⟩ := iso_extension_of_tail G _ hG hk
  have hf := cliqueFree_of_iso G _ hb hfree
  have hc := hcert k b
  cases hw : (cert.getD k.val #[]).getD (boolCode b) default with
  | drop w =>
    rw [hw] at hc
    exact False.elim (cliqueWitnessValid_not_free _ w hc hf)
  | keep target perm mask =>
    rw [hw] at hc
    obtain ⟨hj, hm, hp, he⟩ := hc
    refine ⟨⟨target, hj⟩, iso_trans hb ⟨Equiv.ofBijective _ hp, ?_⟩⟩
    intro i j
    rw [← hm] at he
    simpa only [Equiv.ofBijective_apply, Fin.getElem_fin,
      ← Array.getElem_eq_getD (xs := children) (h := hj) 0] using he i j

#print axioms prunedStepValid_covers
end LittlewoodCylinders.Upper.GraphCover
