import UpperFiveDirections

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace

/-- Only positive rescaling of the original directions is needed. There is
no projective change of the ambient Euclidean metric. -/
theorem triple_ratio_x (a b c d e : Space) :
    triple a b d * triple b c e - triple a b e * triple b c d =
      triple a b c * triple b d e := by
  simp only [triple]
  ring

theorem triple_ratio_y (a b c d e : Space) :
    triple a b d * (-triple a c e) - triple a b e * (-triple a c d) =
      -triple a b c * triple a d e := by
  simp only [triple]
  ring

theorem cross_ne_zero_of_triple_middle {a b c : Space} (h : triple a b c ≠ 0) :
    cross a c ≠ 0 := by
  intro hz
  have heq : triple a b c = -(b 0 * (cross a c) 0 + b 1 * (cross a c) 1 +
      b 2 * (cross a c) 2) := by
    simp [triple, cross]
    ring
  rw [hz] at heq
  simp at heq
  exact h heq

theorem contact_rescale (u m : Fin 5 → Space) (s : Fin 5 → ℝ) (i j : Fin 5) :
    contact (fun k => s k • u k) (fun k => s k • m k) i j =
      s i * s j * contact u m i j := by
  simp only [contact, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The forbidden five-direction sign pattern, without any normalization
hypothesis. Eight determinant signs and nine contact signs suffice. -/
theorem five_sign_obstruction (u m : Fin 5 → Space)
    (h012 : 0 < triple (u 0) (u 1) (u 2))
    (h013 : 0 < triple (u 0) (u 1) (u 3))
    (h014 : 0 < triple (u 0) (u 1) (u 4))
    (h023 : triple (u 0) (u 2) (u 3) < 0)
    (h034 : triple (u 0) (u 3) (u 4) < 0)
    (h123 : 0 < triple (u 1) (u 2) (u 3))
    (h124 : 0 < triple (u 1) (u 2) (u 4))
    (h134 : triple (u 1) (u 3) (u 4) < 0)
    (hdiag : ∀ i, contact u m i i = 0)
    (hT : ∀ i j : Fin 5, i < j → i < 3 →
      contact u m i j = (if i = 0 ∧ j = 3 then -1 else 1) * ‖cross (u i) (u j)‖) :
    False := by
  let A := triple (u 1) (u 2) (u 3)
  let B := -triple (u 0) (u 2) (u 3)
  let C := triple (u 0) (u 1) (u 3)
  let D := triple (u 0) (u 1) (u 2)
  let P := triple (u 1) (u 2) (u 4)
  let Q := -triple (u 0) (u 2) (u 4)
  let R := triple (u 0) (u 1) (u 4)
  have hA : 0 < A := h123
  have hB : 0 < B := neg_pos.mpr h023
  have hC : 0 < C := h013
  have hD : 0 < D := h012
  have hP : 0 < P := h124
  have hR : 0 < R := h014
  let x := C * P / (R * A)
  let y := C * Q / (R * B)
  have hx : 0 < x := div_pos (mul_pos hC hP) (mul_pos hR hA)
  have hratioX : C * P - R * A = D * triple (u 1) (u 3) (u 4) :=
    triple_ratio_x (u 0) (u 1) (u 2) (u 3) (u 4)
  have hratioY : C * Q - R * B = -D * triple (u 0) (u 3) (u 4) :=
    triple_ratio_y (u 0) (u 1) (u 2) (u 3) (u 4)
  have hx₁ : x < 1 := by
    apply (div_lt_one (mul_pos hR hA)).mpr
    have hneg := mul_neg_of_pos_of_neg hD h134
    linarith
  have hy : 1 < y := by
    apply (one_lt_div (mul_pos hR hB)).mpr
    have hneg := mul_neg_of_pos_of_neg hD h034
    nlinarith
  let s : Fin 5 → ℝ := ![A, B, C, D, D * C / R]
  have hs (i : Fin 5) : 0 < s i := by
    fin_cases i <;> dsimp [s]
    · exact hA
    · exact hB
    · exact hC
    · exact hD
    · exact div_pos (mul_pos hD hC) hR
  let v : Fin 5 → Space := fun i => s i • u i
  let n : Fin 5 → Space := fun i => s i • m i
  have hrel₃ : A • u 0 + B • u 1 + C • u 2 = D • u 3 := by
    apply sub_eq_zero.mp
    simpa [A, B, C, D, sub_eq_add_neg] using cofactor_relation (u 0) (u 1) (u 2) (u 3)
  have hrel₄ : P • u 0 + Q • u 1 + R • u 2 = D • u 4 := by
    apply sub_eq_zero.mp
    simpa [P, Q, R, D, sub_eq_add_neg] using cofactor_relation (u 0) (u 1) (u 2) (u 4)
  have hcoef₀ : x * A = C / R * P := by
    dsimp [x]
    field_simp [hA.ne', hR.ne']
  have hcoef₁ : y * B = C / R * Q := by
    dsimp [y]
    field_simp [hB.ne', hR.ne']
  have hcoef₂ : C / R * R = C := div_mul_cancel₀ C hR.ne'
  have hcoef₄ : D * C / R = C / R * D := by ring
  have hv₃ : v 3 = v 0 + v 1 + v 2 := hrel₃.symm
  have hv₄ : v 4 = x • v 0 + y • v 1 + v 2 := by
    dsimp [v, s]
    rw [smul_smul, smul_smul, hcoef₀, hcoef₁, hcoef₄]
    simpa only [smul_add, smul_smul, hcoef₂] using
      congrArg (fun z : Space => (C / R) • z) hrel₄.symm
  have hvne : cross (v 0) (v 3) ≠ 0 := by
    dsimp [v]
    rw [cross_smul_left, cross_smul_right]
    exact smul_ne_zero (hs 0).ne' (smul_ne_zero (hs 3).ne'
      (cross_ne_zero_of_triple_middle h013.ne'))
  apply five_direction_obstruction v n x y hx hx₁ hy hv₃ hv₄ hvne
  · intro i
    change contact (fun k => s k • u k) (fun k => s k • m k) i i = 0
    rw [contact_rescale, hdiag, mul_zero]
  · intro i j hij hi
    change contact (fun k => s k • u k) (fun k => s k • m k) i j = _
    rw [contact_rescale, hT i j hij hi]
    dsimp [v]
    rw [cross_smul_left, cross_smul_right, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos (hs i), abs_of_pos (hs j)]
    ring

#print axioms five_sign_obstruction

end LittlewoodCylinders.Upper
