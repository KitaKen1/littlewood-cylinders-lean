import UpperGraphCover
import Mathlib.Data.Int.Basic

/-! The finite switching checker, kept independent of Euclidean geometry so
large certificates can be reduced without loading the analytic library. -/

namespace LittlewoodCylinders.Upper.GraphCover

theorem zero_ne_succ {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ :=
  (Fin.succ_ne_zero i).symm

def contactOfGraph {n : ℕ} (G : Graph n) (i j : Fin (n + 1)) : ℤ :=
  if i = j then 0 else
    Fin.cases 1 (fun a => Fin.cases 1 (fun b => if G a b then -1 else 1) j) i

theorem contactOfGraph_relabel {n : ℕ} (G H : Graph n) (p : Equiv.Perm (Fin n))
    (hp : ∀ i j, G i j = H (p i) (p j)) :
    ∀ i j, contactOfGraph G i j = contactOfGraph H (liftPerm p i) (liftPerm p j) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [contactOfGraph, hp, zero_ne_succ]

structure SwitchWitness where
  target : ℕ
  permCode : ℕ
  flipCode : ℕ
  negative : Bool
deriving Inhabited

def SwitchWitness.flips (w : SwitchWitness) (i : Fin 8) : ℤ :=
  if w.flipCode.testBit i.val then -1 else 1

def SwitchWitness.sign (w : SwitchWitness) : ℤ := if w.negative then -1 else 1

def SwitchRowValid (source : ℕ) (targets : Array ℕ) (w : SwitchWitness) : Prop :=
    w.target < targets.size ∧ Function.Bijective (decodePerm 8 w.permCode) ∧
    ∀ i j, contactOfGraph (maskGraph 7 (targets.getD w.target 0)) i j =
      w.sign * w.flips i * w.flips j * contactOfGraph (maskGraph 7 source)
        (decodePerm 8 w.permCode i) (decodePerm 8 w.permCode j)

instance (source : ℕ) (targets : Array ℕ) (w : SwitchWitness) :
    Decidable (SwitchRowValid source targets w) := inferInstanceAs (Decidable (_ ∧ _))

def SwitchValid (sources targets : Array ℕ) (cert : Array SwitchWitness) : Prop :=
  ∀ k : Fin sources.size, SwitchRowValid sources[k] targets (cert.getD k.val default)

instance (sources targets : Array ℕ) (cert : Array SwitchWitness) :
    Decidable (SwitchValid sources targets cert) := inferInstanceAs (Decidable (∀ _, _))

end LittlewoodCylinders.Upper.GraphCover
