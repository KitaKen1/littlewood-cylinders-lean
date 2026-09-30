import Mathlib.Tactic.Sat.FromLRAT
import UpperNecessarySigns

/-! A SAT clause forbids a partial orientation assignment. Only the logical
meaning of the clause is used: SAT search is not part of the trusted base. -/
namespace LittlewoodCylinders.Upper.SAT

open Sat

deriving instance DecidableEq for Literal

/-- Sparse base-eight indexing avoids trusting a table of triple ranks. -/
def index (a b c : Fin 8) : ℕ := 64 * a.val + 8 * b.val + c.val

def decode (n : ℕ) : Fin 8 × Fin 8 × Fin 8 :=
  (⟨n / 64 % 8, Nat.mod_lt _ (by decide)⟩,
   ⟨n / 8 % 8, Nat.mod_lt _ (by decide)⟩,
   ⟨n % 8, Nat.mod_lt _ (by decide)⟩)

theorem decode_index : ∀ a b c : Fin 8, decode (index a b c) = (a, b, c) := by
  decide +kernel

def valuation (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) : Valuation :=
  fun n => χ (decode n).1 (decode n).2.1 (decode n).2.2 = 1

@[simp] theorem valuation_index (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (a b c : Fin 8) :
    valuation χ (index a b c) ↔ χ a b c = 1 := by
  simp [valuation, decode_index]

def partialOrientation (cl : List Literal) (a b c : Fin 8) : ℤ :=
  if .neg (index a b c) ∈ cl then 1 else
  if .pos (index a b c) ∈ cl then -1 else 0

def Agrees (χ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ) : Prop :=
  ∀ a b c, a < b → b < c → ψ a b c ≠ 0 → χ a b c = ψ a b c

theorem neg_of_not_satisfies (v : Valuation) (cl : List Literal)
    (h : ¬v.satisfies cl) : ∀ l ∈ cl, v.neg l := by
  induction cl with
  | nil => simp
  | cons l ls ih =>
    have hh : v.neg l ∧ ¬v.satisfies ls := by
      simpa only [Valuation.satisfies, Classical.not_imp] using h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh.1
    · exact ih hh.2 x hx

theorem agrees_of_not_satisfies (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1)
    (cl : List Literal) (h : ¬(valuation χ).satisfies cl) :
    Agrees χ (partialOrientation cl) := by
  intro a b c _ _ hn
  unfold partialOrientation at hn ⊢
  split_ifs at hn ⊢ with hp hm
  · have hh := neg_of_not_satisfies _ _ h (.neg (index a b c)) hp
    simpa only [Valuation.neg, valuation_index] using hh
  · have hh := neg_of_not_satisfies _ _ h (.pos (index a b c)) hm
    have hh' : χ a b c ≠ 1 := by
      simpa only [Valuation.neg, valuation_index] using hh
    exact (hu a b c).resolve_left hh'
  · exact (hn rfl).elim

theorem Agrees.alternating {χ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ} (h : Agrees χ ψ)
    (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hn : alternatingSign ψ a b c ≠ 0) :
    alternatingSign χ a b c = alternatingSign ψ a b c := by
  unfold alternatingSign at hn ⊢
  split_ifs at hn ⊢ with h₁ h₂ h₃ h₄ h₅
  all_goals first
    | exact h _ _ _ (by omega) (by omega) hn
    | exact congrArg Neg.neg (h _ _ _ (by omega) (by omega) (by simpa using hn))

theorem Agrees.minors {χ ψ : Fin 8 → Fin 8 → Fin 8 → ℤ} (h : Agrees χ ψ)
    (I : Fin 4 → Fin 8) (hI : StrictMono I) (hn : ∀ i, signedMinors ψ I i ≠ 0) :
    signedMinors χ I = signedMinors ψ I := by
  have h₀ := hn 0
  have h₁ := hn 1
  have h₂ := hn 2
  have h₃ := hn 3
  simp [signedMinors] at h₀ h₁ h₂ h₃
  have e₀ := h (I 1) (I 2) (I 3) (hI (by decide)) (hI (by decide)) h₀
  have e₁ := h (I 0) (I 2) (I 3) (hI (by decide)) (hI (by decide)) h₁
  have e₂ := h (I 0) (I 1) (I 3) (hI (by decide)) (hI (by decide)) h₂
  have e₃ := h (I 0) (I 1) (I 2) (hI (by decide)) (hI (by decide)) h₃
  simp only [signedMinors, e₀, e₁, e₂, e₃]

#print axioms agrees_of_not_satisfies
#print axioms Agrees.minors

end LittlewoodCylinders.Upper.SAT
