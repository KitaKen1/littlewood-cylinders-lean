import UpperFiveNormalization
import UpperAlternating

namespace LittlewoodCylinders.Upper

def fiveOrientation (i j : Fin 5) : ℤ :=
  if (i = 0 ∧ 2 ≤ j) ∨ (i = 1 ∧ j = 3) then -1 else 1

structure FiveCertificate where
  labels : Fin 5 → Fin 8
  signs : Fin 5 → ℤ
  globalSign : ℤ

structure FiveRecord where
  matrixId : Nat
  orbitId : Nat
  E : Fin 8 → Fin 8 → ℤ
  χ : Fin 8 → Fin 8 → Fin 8 → ℤ
  witness : FiveCertificate

def FiveRecord.Valid (r : FiveRecord) : Prop :=
  Function.Injective r.witness.labels ∧
  (∀ i, r.witness.signs i = 1 ∨ r.witness.signs i = -1) ∧
  (r.witness.globalSign = 1 ∨ r.witness.globalSign = -1) ∧
  (∀ i j : Fin 5, i < j → i < 3 →
    r.witness.globalSign * r.witness.signs i * r.witness.signs j *
      r.E (r.witness.labels i) (r.witness.labels j) = if i = 0 ∧ j = 3 then -1 else 1) ∧
  ∀ i j k : Fin 5, i < j → j < k →
    r.witness.signs i * r.witness.signs j * r.witness.signs k * fiveOrientation i j =
      alternatingSign r.χ (r.witness.labels i) (r.witness.labels j) (r.witness.labels k)

instance (r : FiveRecord) : Decidable r.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Soundness of a five-direction certificate, including the relabeling,
orientation switches, and global contact-sign switch. -/
theorem fiveRecord_sound (r : FiveRecord) (hr : r.Valid) (u m : Fin 8 → Space)
    (hT : ∀ a b, contact u m a b = (r.E a b : ℝ) * ‖cross (u a) (u b)‖)
    (hχ : ∀ a b c, a < b → b < c →
      0 < (r.χ a b c : ℝ) * triple (u a) (u b) (u c)) : False := by
  obtain ⟨hinj, hs, _hg, hpairs, htriples⟩ := hr
  let I := r.witness.labels
  let s : Fin 5 → ℝ := fun i => (r.witness.signs i : ℝ)
  let g : ℝ := (r.witness.globalSign : ℝ)
  let v : Fin 5 → Space := fun i => s i • u (I i)
  let n : Fin 5 → Space := fun i => (g * s i) • m (I i)
  have hsabs (i : Fin 5) : |s i| = 1 := by
    rcases hs i with hh | hh <;> simp [s, hh]
  have htr (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
      0 < (fiveOrientation i j : ℝ) * triple (v i) (v j) (v k) := by
    have hab : I i ≠ I j := fun h => hij.ne (hinj h)
    have hac : I i ≠ I k := fun h => (lt_trans hij hjk).ne (hinj h)
    have hbc : I j ≠ I k := fun h => hjk.ne (hinj h)
    have hh := alternatingSign_positive u r.χ hχ (I i) (I j) (I k) hab hac hbc
    have heq := congrArg (fun z : ℤ => (z : ℝ)) (htriples i j k hij hjk)
    push_cast at heq
    dsimp [v]
    rw [triple_rescale]
    have hid : (fiveOrientation i j : ℝ) * (s i * s j * s k * triple (u (I i)) (u (I j)) (u (I k))) =
        (alternatingSign r.χ (I i) (I j) (I k) : ℝ) * triple (u (I i)) (u (I j)) (u (I k)) := by
      rw [← heq]
      dsimp [s]
      ring
    rw [hid]
    exact hh
  have hpair (i j : Fin 5) : contact v n i j = g * s i * s j * contact u m (I i) (I j) := by
    simp only [contact, v, n, real_inner_smul_left, real_inner_smul_right]
    ring
  have hnorm (i j : Fin 5) : ‖cross (v i) (v j)‖ = ‖cross (u (I i)) (u (I j))‖ := by
    dsimp [v]
    rw [cross_smul_left, cross_smul_right, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, hsabs, one_mul]
  apply five_sign_obstruction v n
  · simpa [fiveOrientation] using htr 0 1 2 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 0 1 3 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 0 1 4 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 0 2 3 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 0 3 4 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 1 2 3 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 1 2 4 (by decide) (by decide)
  · simpa [fiveOrientation] using htr 1 3 4 (by decide) (by decide)
  · intro i
    rw [hpair, hT]
    simp
  · intro i j hij hi
    rw [hpair, hT, hnorm]
    have heq := congrArg (fun z : ℤ => (z : ℝ)) (hpairs i j hij hi)
    push_cast at heq
    have hid : g * s i * s j * ((r.E (I i) (I j) : ℝ) * ‖cross (u (I i)) (u (I j))‖) =
        (g * s i * s j * (r.E (I i) (I j) : ℝ)) * ‖cross (u (I i)) (u (I j))‖ := by ring
    rw [hid]
    dsimp [g, s, I]
    rw [heq]

#print axioms fiveRecord_sound

end LittlewoodCylinders.Upper
