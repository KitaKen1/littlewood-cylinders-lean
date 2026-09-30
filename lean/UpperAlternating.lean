import UpperOrientation

namespace LittlewoodCylinders.Upper

theorem triple_cycle (a b c : Space) : triple a b c = triple b c a := by
  simp only [triple]
  ring

theorem triple_swap_last (a b c : Space) : triple a b c = -triple a c b := by
  simp only [triple]
  ring

theorem triple_rescale (a b c : Space) (r s t : ℝ) :
    triple (r • a) (s • b) (t • c) = r * s * t * triple a b c := by
  simp [triple]
  ring

/-- Extend the table of increasing triples by alternation. -/
def alternatingSign (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (a b c : Fin 8) : ℤ :=
  if a < b then
    if b < c then χ a b c else if a < c then -χ a c b else χ c a b
  else if a < c then -χ b a c else if b < c then χ b c a else -χ c b a

theorem alternatingSign_positive (u : Fin 8 → Space) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c))
    (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    0 < (alternatingSign χ a b c : ℝ) * triple (u a) (u b) (u c) := by
  unfold alternatingSign
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · exact hχ a b c h₁ h₂
  · have hh := hχ a c b h₃ (by omega)
    rw [triple_swap_last (u a) (u b) (u c)]
    simpa using hh
  · have hh := hχ c a b (by omega) h₁
    rw [triple_cycle (u a) (u b) (u c), triple_cycle (u b) (u c) (u a)]
    exact hh
  · have hh := hχ b a c (by omega) h₄
    rw [triple_swap_last (u a) (u b) (u c), triple_cycle (u a) (u c) (u b),
      triple_cycle (u c) (u b) (u a)]
    simpa using hh
  · have hh := hχ b c a h₅ (by omega)
    rw [triple_cycle (u a) (u b) (u c)]
    exact hh
  · have hh := hχ c b a (by omega) (by omega)
    rw [triple_swap_last (u a) (u b) (u c), triple_cycle (u a) (u c) (u b)]
    simpa using hh

#print axioms alternatingSign_positive

theorem uniform_of_sorted_signs (u : Fin 8 → Space) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c)) :
    ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0 := by
  intro a b c hab hac hbc hz
  have hh := alternatingSign_positive u χ hχ a b c hab hac hbc
  simp [hz] at hh

end LittlewoodCylinders.Upper
