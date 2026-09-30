import UpperCircuit

namespace LittlewoodCylinders.Upper

/-- A small, untrusted witness. Its mathematical meaning is supplied by
`polygonCertificate_sound`, not by the program that found it. -/
structure PolygonCertificate where
  I : Fin 4 → Fin 8
  J : Fin 4 → Fin 8
  cSign : Fin 4 → ℤ
  dSign : Fin 4 → ℤ
  globalSign : ℤ

def PolygonCertificate.row (w : PolygonCertificate) (E : Fin 8 → Fin 8 → ℤ)
    (j i : Fin 4) : Bool :=
  decide (0 ≤ w.globalSign * w.dSign j * w.cSign i * E (w.J j) (w.I i))

/-- All discrete checks, including sign units and injectivity, are kernel-decidable. -/
def PolygonCertificate.Valid (w : PolygonCertificate) (E : Fin 8 → Fin 8 → ℤ) : Prop :=
  Function.Injective w.I ∧ Function.Injective w.J ∧
  (∀ i, w.cSign i = 1 ∨ w.cSign i = -1) ∧
  (∀ j, w.dSign j = 1 ∨ w.dSign j = -1) ∧
  (w.globalSign = 1 ∨ w.globalSign = -1) ∧
  (∀ a b, a ≠ b → |E a b| = 1) ∧
  ∀ j, majorityCheck (w.row E j) = true

instance (w : PolygonCertificate) (E : Fin 8 → Fin 8 → ℤ) :
    Decidable (w.Valid E) := inferInstanceAs (Decidable (_ ∧ _))

theorem eq_sign_mul_abs (s : ℤ) (x : ℝ) (hs : s = 1 ∨ s = -1)
    (h : 0 < (s : ℝ) * x) : x = (s : ℝ) * |x| := by
  rcases hs with rfl | rfl
  · norm_num at h ⊢
    exact (abs_of_pos h).symm
  · norm_num at h ⊢
    rw [abs_of_neg (by linarith)]
    ring

/-- A checked polygon witness rules out every uniform geometric realization
with the specified contact and cofactor signs. No coordinate search is used. -/
theorem polygonCertificate_sound (E : Fin 8 → Fin 8 → ℤ) (w : PolygonCertificate)
    (hw : w.Valid E) (u m : Fin 8 → Space)
    (hdet : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0)
    (hT : ∀ a b, contact u m a b = (E a b : ℝ) * ‖cross (u a) (u b)‖)
    (hcs : ∀ i, 0 < (w.cSign i : ℝ) * cofactors (u ∘ w.I) i)
    (hds : ∀ j, 0 < (w.dSign j : ℝ) * cofactors (u ∘ w.J) j) : False := by
  obtain ⟨hI, _hJ, hcunit, hdunit, hgunit, hEunit, hcheck⟩ := hw
  let c := cofactors (u ∘ w.I)
  let d := cofactors (u ∘ w.J)
  have hcnz (i : Fin 4) : c i ≠ 0 := by
    intro hz
    have h := hcs i
    change 0 < (w.cSign i : ℝ) * c i at h
    simp [hz] at h
  have hdnz (j : Fin 4) : d j ≠ 0 := by
    intro hz
    have h := hds j
    change 0 < (w.dSign j : ℝ) * d j at h
    simp [hz] at h
  have hcabs (i : Fin 4) : c i = (w.cSign i : ℝ) * |c i| :=
    eq_sign_mul_abs _ _ (hcunit i) (hcs i)
  have hdabs (j : Fin 4) : d j = (w.dSign j : ℝ) * |d j| :=
    eq_sign_mul_abs _ _ (hdunit j) (hds j)
  have hmag (a b : Fin 8) : |contact u m a b| = ‖cross (u a) (u b)‖ := by
    rw [hT, abs_mul, abs_norm]
    by_cases hab : a = b
    · subst b
      simp
    · have hunit : |(E a b : ℝ)| = 1 := by exact_mod_cast hEunit a b hab
      rw [hunit, one_mul]
  have hg : |(w.globalSign : ℝ)| = 1 := by
    rcases hgunit with hg | hg <;> simp [hg]
  apply polygon_obstruction u m hdet w.I w.J hI c d
    (cofactors_sum (u ∘ w.I)) (cofactors_sum (u ∘ w.J)) hcnz hdnz hmag
    (w.globalSign : ℝ) hg (w.row E) hcheck
  intro j i
  have heq : (w.globalSign : ℝ) * d j * c i * contact u m (w.J j) (w.I i) =
      ((w.globalSign * w.dSign j * w.cSign i * E (w.J j) (w.I i) : ℤ) : ℝ) *
      (|d j| * |c i| * ‖cross (u (w.J j)) (u (w.I i))‖) := by
    conv_lhs => rw [hT, hdabs j, hcabs i]
    push_cast
    ring
  have hn : 0 ≤ |d j| * |c i| * ‖cross (u (w.J j)) (u (w.I i))‖ := by positivity
  by_cases h : 0 ≤ w.globalSign * w.dSign j * w.cSign i * E (w.J j) (w.I i)
  · simp only [PolygonCertificate.row, h, decide_true, ↓reduceIte]
    rw [heq]
    exact mul_nonneg (by exact_mod_cast h) hn
  · simp only [PolygonCertificate.row, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_not_ge h)) hn

#print axioms polygonCertificate_sound

end LittlewoodCylinders.Upper
