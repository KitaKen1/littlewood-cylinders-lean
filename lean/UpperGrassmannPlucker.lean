import UpperAlternating

/-! The determinant sign clauses used in `research/sign_obstruction_sat.py`.
The identity is checked by polynomial normalization; its sign consequence uses
only the positivity supplied by the orientation table. -/

namespace LittlewoodCylinders.Upper

theorem grassmann_plucker (a b c d e : Space) :
    triple a b c * triple a d e - triple a b d * triple a c e +
      triple a b e * triple a c d = 0 := by
  simp only [triple]
  ring

/-- Three nonzero terms summing to zero have both signs. The integers only
specify the signs; they need not have unit magnitude. -/
theorem signs_mixed_of_sum_zero (s t v : ℤ) (x y z : ℝ)
    (hs : 0 < (s : ℝ) * x) (ht : 0 < (t : ℝ) * y) (hv : 0 < (v : ℝ) * z)
    (hzero : x + y + z = 0) :
    (0 < s ∨ 0 < t ∨ 0 < v) ∧ (s < 0 ∨ t < 0 ∨ v < 0) := by
  have hsr := mul_pos_iff.mp hs
  have htr := mul_pos_iff.mp ht
  have hvr := mul_pos_iff.mp hv
  constructor
  · by_contra h
    push Not at h
    have hs' : (s : ℝ) ≤ 0 := by exact_mod_cast h.1
    have ht' : (t : ℝ) ≤ 0 := by exact_mod_cast h.2.1
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast h.2.2
    rcases hsr with hsr | hsr <;> rcases htr with htr | htr <;>
      rcases hvr with hvr | hvr <;> linarith
  · by_contra h
    push Not at h
    have hs' : 0 ≤ (s : ℝ) := by exact_mod_cast h.1
    have ht' : 0 ≤ (t : ℝ) := by exact_mod_cast h.2.1
    have hv' : 0 ≤ (v : ℝ) := by exact_mod_cast h.2.2
    rcases hsr with hsr | hsr <;> rcases htr with htr | htr <;>
      rcases hvr with hvr | hvr <;> linarith

/-- The two SAT clauses: at least one term is positive and at least one is
negative. The middle determinant product carries a minus sign. -/
def gpCheck (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (a b c d e : Fin 8) : Bool :=
  let s := alternatingSign χ a b c * alternatingSign χ a d e
  let t := -(alternatingSign χ a b d * alternatingSign χ a c e)
  let v := alternatingSign χ a b e * alternatingSign χ a c d
  decide ((0 < s ∨ 0 < t ∨ 0 < v) ∧ (s < 0 ∨ t < 0 ∨ v < 0))

theorem signed_mul_pos {s t : ℤ} {x y : ℝ}
    (hs : 0 < (s : ℝ) * x) (ht : 0 < (t : ℝ) * y) :
    0 < ((s * t : ℤ) : ℝ) * (x * y) := by
  calc
    0 < ((s : ℝ) * x) * ((t : ℝ) * y) := mul_pos hs ht
    _ = _ := by push_cast; ring

theorem gpCheck_of_sorted_signs (u : Fin 8 → Space)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c))
    (I : Fin 5 → Fin 8) (hI : Function.Injective I) :
    gpCheck χ (I 0) (I 1) (I 2) (I 3) (I 4) = true := by
  have hp (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      0 < (alternatingSign χ (I i) (I j) (I k) : ℝ) *
        triple (u (I i)) (u (I j)) (u (I k)) :=
    alternatingSign_positive u χ hχ _ _ _
      (fun h => hij (hI h)) (fun h => hik (hI h)) (fun h => hjk (hI h))
  let D := fun i j k => triple (u (I i)) (u (I j)) (u (I k))
  let S := fun i j k => alternatingSign χ (I i) (I j) (I k)
  have h₁ := signed_mul_pos (hp 0 1 2 (by decide) (by decide) (by decide))
    (hp 0 3 4 (by decide) (by decide) (by decide))
  have hp₂ := signed_mul_pos (hp 0 1 3 (by decide) (by decide) (by decide))
    (hp 0 2 4 (by decide) (by decide) (by decide))
  have h₃ := signed_mul_pos (hp 0 1 4 (by decide) (by decide) (by decide))
    (hp 0 2 3 (by decide) (by decide) (by decide))
  have h₂ : 0 < ((-(S 0 1 3 * S 0 2 4) : ℤ) : ℝ) * (-(D 0 1 3 * D 0 2 4)) := by
    simpa only [Int.cast_neg, neg_mul_neg] using hp₂
  apply decide_eq_true
  exact signs_mixed_of_sum_zero _ _ _ _ _ _ h₁ h₂ h₃
    (by simpa only [D, sub_eq_add_neg] using
      grassmann_plucker (u (I 0)) (u (I 1)) (u (I 2)) (u (I 3)) (u (I 4)))

#print axioms gpCheck_of_sorted_signs

end LittlewoodCylinders.Upper
