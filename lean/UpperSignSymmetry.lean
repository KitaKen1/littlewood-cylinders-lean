import UpperRecordedCases

/-! Exact symmetries of realizable sign systems. These are witnesses at the
level of the direction and moment vectors, not assumptions about a search. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace

theorem signRealizable_reorient_relabel
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (h : SignRealizable E χ) (p : Equiv.Perm (Fin 8)) (f : Fin 8 → ℤ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    SignRealizable (fun i j => f i * f j * E (p i) (p j))
      (fun a b c => f a * f b * f c * alternatingSign χ (p a) (p b) (p c)) := by
  obtain ⟨u, m, hT, hχ⟩ := h
  refine ⟨fun i => (f i : ℝ) • u (p i), fun i => (f i : ℝ) • m (p i), ?_, ?_⟩
  · intro i j
    have habs (k : Fin 8) : |(f k : ℝ)| = 1 := by
      rcases hf k with hh | hh <;> simp [hh]
    simp only [contact, real_inner_smul_left, real_inner_smul_right,
      cross_smul_left, cross_smul_right, norm_smul, Real.norm_eq_abs, habs,
      one_mul, Int.cast_mul]
    have hh := hT (p i) (p j)
    unfold contact at hh
    calc
      _ = (f i : ℝ) * (f j : ℝ) *
          (⟪u (p i), m (p j)⟫ + ⟪m (p i), u (p j)⟫) := by ring
      _ = _ := by rw [hh]; ring
  · intro a b c hab hbc
    have hp := alternatingSign_positive u χ hχ (p a) (p b) (p c)
      (fun h => hab.ne (p.injective h))
      (fun h => (lt_trans hab hbc).ne (p.injective h))
      (fun h => hbc.ne (p.injective h))
    have hs : ((f a : ℝ) * (f b : ℝ) * (f c : ℝ)) ^ 2 = 1 := by
      rcases hf a with ha | ha <;> rcases hf b with hb | hb <;>
        rcases hf c with hc | hc <;> norm_num [ha, hb, hc]
    rw [triple_rescale]
    push_cast
    calc
      0 < (alternatingSign χ (p a) (p b) (p c) : ℝ) *
          triple (u (p a)) (u (p b)) (u (p c)) := hp
      _ = ((f a : ℝ) * (f b : ℝ) * (f c : ℝ)) ^ 2 *
          ((alternatingSign χ (p a) (p b) (p c) : ℝ) *
            triple (u (p a)) (u (p b)) (u (p c))) := by rw [hs, one_mul]
      _ = _ := by ring

theorem signRealizable_neg_contact
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (h : SignRealizable E χ) : SignRealizable (fun i j => -E i j) χ := by
  obtain ⟨u, m, hT, hχ⟩ := h
  refine ⟨u, fun i => -m i, ?_, hχ⟩
  intro i j
  simpa only [contact, inner_neg_left, inner_neg_right, ← neg_add, Int.cast_neg,
    neg_mul] using congrArg Neg.neg (hT i j)

theorem signRealizable_neg_orientation
    (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (h : SignRealizable E χ) : SignRealizable E (fun a b c => -χ a b c) := by
  obtain ⟨u, m, hT, hχ⟩ := h
  refine ⟨fun i => (-1 : ℝ) • u i, fun i => (-1 : ℝ) • m i, ?_, ?_⟩
  · intro i j
    simpa only [contact, real_inner_smul_left, real_inner_smul_right,
      cross_smul_left, cross_smul_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_one, one_mul, neg_one_mul, neg_neg] using hT i j
  · intro a b c hab hbc
    simpa only [triple_rescale, Int.cast_neg, neg_one_mul, mul_neg_one, neg_neg,
      neg_mul_neg, one_mul] using hχ a b c hab hbc

#print axioms signRealizable_reorient_relabel
#print axioms signRealizable_neg_contact
#print axioms signRealizable_neg_orientation

end LittlewoodCylinders.Upper
