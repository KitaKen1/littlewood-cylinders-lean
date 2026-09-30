import UpperSignCertificate

namespace LittlewoodCylinders.Upper

def signedMinors (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8) : Fin 4 → ℤ :=
  ![χ (I 1) (I 2) (I 3), -χ (I 0) (I 2) (I 3),
    χ (I 0) (I 1) (I 3), -χ (I 0) (I 1) (I 2)]

theorem cofactors_positive_of_signs (u : Fin 8 → Space)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8) (hI : StrictMono I)
    (hχ : ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c)) :
    ∀ i, 0 < (signedMinors χ I i : ℝ) * cofactors (u ∘ I) i := by
  intro i
  fin_cases i
  · simpa [signedMinors, cofactors, Function.comp_def] using
      hχ (I 1) (I 2) (I 3) (hI (by decide)) (hI (by decide))
  · simpa [signedMinors, cofactors, Function.comp_def] using
      hχ (I 0) (I 2) (I 3) (hI (by decide)) (hI (by decide))
  · simpa [signedMinors, cofactors, Function.comp_def] using
      hχ (I 0) (I 1) (I 3) (hI (by decide)) (hI (by decide))
  · simpa [signedMinors, cofactors, Function.comp_def] using
      hχ (I 0) (I 1) (I 2) (hI (by decide)) (hI (by decide))

/-- Lexicographic storage of the 56 increasing triples. All uses of this
encoding in a certificate are evaluated by Lean's kernel. -/
def orientationFromArray (v : Array ℤ) (a b c : Fin 8) : ℤ :=
  v.getD ((56 - (8 - a.val).choose 3) +
    ((7 - a.val).choose 2 - (8 - b.val).choose 2) + (c.val - b.val - 1)) 0

structure PolygonRecord where
  matrixId : Nat
  orbitId : Nat
  E : Fin 8 → Fin 8 → ℤ
  χ : Fin 8 → Fin 8 → Fin 8 → ℤ
  witness : PolygonCertificate

def PolygonRecord.Valid (r : PolygonRecord) : Prop :=
  r.witness.Valid r.E ∧ StrictMono r.witness.I ∧ StrictMono r.witness.J ∧
  r.witness.cSign = signedMinors r.χ r.witness.I ∧
  r.witness.dSign = signedMinors r.χ r.witness.J

instance (r : PolygonRecord) : Decidable r.Valid :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Soundness of a record, now stated directly with determinant signs rather
than assuming the signs of the circuit coefficients. -/
theorem polygonRecord_sound (r : PolygonRecord) (hr : r.Valid) (u m : Fin 8 → Space)
    (hdet : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → triple (u a) (u b) (u c) ≠ 0)
    (hT : ∀ a b, contact u m a b = (r.E a b : ℝ) * ‖cross (u a) (u b)‖)
    (hχ : ∀ a b c, a < b → b < c →
      0 < (r.χ a b c : ℝ) * triple (u a) (u b) (u c)) : False := by
  obtain ⟨hw, hI, hJ, hc, hd⟩ := hr
  apply polygonCertificate_sound r.E r.witness hw u m hdet hT
  · rw [hc]
    exact cofactors_positive_of_signs u r.χ r.witness.I hI hχ
  · rw [hd]
    exact cofactors_positive_of_signs u r.χ r.witness.J hJ hχ

#print axioms polygonRecord_sound

end LittlewoodCylinders.Upper
