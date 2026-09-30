import UpperAlternating

/-! The four-direction SAT constraint is the existing polygon obstruction
with the same four-circuit on both sides. A six-bit characterization below
checks its agreement with the edge-count rule used by the Python enumerator. -/

namespace LittlewoodCylinders.Upper

def tetrahedronWitness (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (I : Fin 4 → Fin 8) (g : ℤ) : PolygonCertificate :=
  ⟨I, I, signedMinors χ I, signedMinors χ I, g⟩

def tetrahedronCheck (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8) : Bool :=
  !(decide (∀ j, majorityCheck ((tetrahedronWitness χ I 1).row E j) = true)) &&
  !(decide (∀ j, majorityCheck ((tetrahedronWitness χ I (-1)).row E j) = true))

theorem signedMinors_unit (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hχ : ∀ a b c, a < b → b < c → χ a b c = 1 ∨ χ a b c = -1)
    (I : Fin 4 → Fin 8) (hI : StrictMono I) :
    ∀ i, signedMinors χ I i = 1 ∨ signedMinors χ I i = -1 := by
  intro i
  fin_cases i
  · simpa [signedMinors] using hχ (I 1) (I 2) (I 3) (hI (by decide)) (hI (by decide))
  · rcases hχ (I 0) (I 2) (I 3) (hI (by decide)) (hI (by decide)) with h | h <;>
      simp [signedMinors, h]
  · simpa [signedMinors] using hχ (I 0) (I 1) (I 3) (hI (by decide)) (hI (by decide))
  · rcases hχ (I 0) (I 1) (I 2) (hI (by decide)) (hI (by decide)) with h | h <;>
      simp [signedMinors, h]

theorem tetrahedronCheck_of_realization (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (u m : Fin 8 → Space)
    (hE : ∀ a b, a ≠ b → |E a b| = 1)
    (hχunit : ∀ a b c, a < b → b < c → χ a b c = 1 ∨ χ a b c = -1)
    (hT : ∀ a b, contact u m a b = (E a b : ℝ) * ‖cross (u a) (u b)‖)
    (hχ : ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c))
    (I : Fin 4 → Fin 8) (hI : StrictMono I) : tetrahedronCheck E χ I = true := by
  have hexclude (g : ℤ) (hg : g = 1 ∨ g = -1) :
      ¬ (∀ j, majorityCheck ((tetrahedronWitness χ I g).row E j) = true) := by
    intro hcheck
    have hw : (tetrahedronWitness χ I g).Valid E :=
      ⟨hI.injective, hI.injective, signedMinors_unit χ hχunit I hI,
        signedMinors_unit χ hχunit I hI, hg, hE, hcheck⟩
    exact polygonCertificate_sound E _ hw u m (uniform_of_sorted_signs u χ hχ) hT
      (cofactors_positive_of_signs u χ I hI hχ) (cofactors_positive_of_signs u χ I hI hχ)
  simp only [tetrahedronCheck, hexclude 1 (Or.inl rfl), hexclude (-1) (Or.inr rfl),
    decide_false, Bool.not_false, Bool.and_self]

/-- Edge order: 01, 02, 03, 12, 13, 23. The diagonal is always positive
because its contact value is zero. -/
def tetraRows (b : Fin 6 → Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, b 0, b 1, b 2], ![b 0, true, b 3, b 4],
    ![b 1, b 3, true, b 5], ![b 2, b 4, b 5, true]]

def tetraBitsCheck (b : Fin 6 → Bool) : Bool :=
  !(decide (∀ j, majorityCheck (tetraRows b j) = true)) &&
  !(decide (∀ j, majorityCheck (tetraRows (fun k => !(b k)) j) = true))

/-- Exactly the edge-count condition used by the Python SAT generator.
For two edges of the minority sign, opposite edges are forbidden. -/
def tetraCountCheck (b : Fin 6 → Bool) : Bool :=
  let k := (List.ofFn b).count true
  let opposite := fun s : Fin 6 → Bool => (s 0 && s 5) || (s 1 && s 4) || (s 2 && s 3)
  decide (k = 2 ∨ k = 3 ∨ k = 4) &&
    !(decide (k = 2) && opposite b) &&
    !(decide (k = 4) && opposite (fun i => !(b i)))

theorem tetra_bits_eq_count : ∀ b : Fin 6 → Bool, tetraBitsCheck b = tetraCountCheck b := by
  decide +kernel

/-- The six entries of a symmetric four-by-four sign matrix. Nonnegative
means positive whenever the off-diagonal entries are nonzero. -/
def tetraEdgeBits (B : Fin 4 → Fin 4 → ℤ) : Fin 6 → Bool :=
  ![decide (0 ≤ B 0 1), decide (0 ≤ B 0 2), decide (0 ≤ B 0 3),
    decide (0 ≤ B 1 2), decide (0 ≤ B 1 3), decide (0 ≤ B 2 3)]

theorem tetraRows_of_matrix (B : Fin 4 → Fin 4 → ℤ)
    (hdiag : ∀ i, B i i = 0) (hsym : ∀ i j, B i j = B j i) :
    (fun j i => decide (0 ≤ B j i)) = tetraRows (tetraEdgeBits B) := by
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [tetraRows, tetraEdgeBits, hdiag, hsym 1 0, hsym 2 0, hsym 3 0,
      hsym 2 1, hsym 3 1, hsym 3 2, Matrix.cons_val_two]

theorem tetraEdgeBits_neg (B : Fin 4 → Fin 4 → ℤ)
    (hnz : ∀ i j, i ≠ j → B i j ≠ 0) :
    tetraEdgeBits (fun j i => -B j i) = fun k => !(tetraEdgeBits B k) := by
  have hh (i j : Fin 4) (hij : i ≠ j) :
      decide (0 ≤ -B i j) = !(decide (0 ≤ B i j)) := by
    have hz := hnz i j hij
    by_cases h : 0 ≤ B i j
    · have hn : ¬ 0 ≤ -B i j := by omega
      simp only [h, hn, decide_false, decide_true, Bool.not_true]
    · have hn : 0 ≤ -B i j := by omega
      simp only [h, hn, decide_false, decide_true, Bool.not_false]
  funext k
  fin_cases k <;> apply hh <;> decide

/-- Integer edge signs after the cofactor reorientation. -/
def tetraMatrix (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8) (j i : Fin 4) : ℤ :=
  signedMinors χ I j * signedMinors χ I i * E (I j) (I i)

theorem tetrahedronCheck_eq_count (E : Fin 8 → Fin 8 → ℤ)
    (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) (I : Fin 4 → Fin 8)
    (hdiag : ∀ i, E i i = 0) (hsym : ∀ i j, E i j = E j i)
    (hE : ∀ i j, i ≠ j → |E i j| = 1)
    (hχ : ∀ a b c, a < b → b < c → χ a b c = 1 ∨ χ a b c = -1)
    (hI : StrictMono I) :
    tetrahedronCheck E χ I = tetraCountCheck (tetraEdgeBits (tetraMatrix E χ I)) := by
  let B := tetraMatrix E χ I
  have hBdiag (i : Fin 4) : B i i = 0 := by simp [B, tetraMatrix, hdiag]
  have hBsym (j i : Fin 4) : B j i = B i j := by
    dsimp [B, tetraMatrix]
    rw [hsym (I j) (I i)]
    ring
  have hsnz (i : Fin 4) : signedMinors χ I i ≠ 0 := by
    rcases signedMinors_unit χ hχ I hI i with h | h <;> simp [h]
  have hBnz (j i : Fin 4) (hji : j ≠ i) : B j i ≠ 0 := by
    have he := hE (I j) (I i) (fun h => hji (hI.injective h))
    have he' : E (I j) (I i) ≠ 0 := by intro hz; simp [hz] at he
    exact mul_ne_zero (mul_ne_zero (hsnz j) (hsnz i)) he'
  have hpos : (tetrahedronWitness χ I 1).row E = tetraRows (tetraEdgeBits B) := by
    funext j i
    simpa only [PolygonCertificate.row, tetrahedronWitness, one_mul, B, tetraMatrix] using
      congrFun (congrFun (tetraRows_of_matrix B hBdiag hBsym) j) i
  have hneg : (tetrahedronWitness χ I (-1)).row E =
      tetraRows (fun k => !(tetraEdgeBits B k)) := by
    have hh := tetraRows_of_matrix (fun j i => -B j i)
      (by intro i; rw [hBdiag, neg_zero]) (by intro i j; rw [hBsym i j])
    rw [tetraEdgeBits_neg B hBnz] at hh
    funext j i
    simpa only [PolygonCertificate.row, tetrahedronWitness, neg_one_mul, neg_mul, one_mul,
      B, tetraMatrix] using congrFun (congrFun hh j) i
  rw [tetrahedronCheck, hpos, hneg]
  exact tetra_bits_eq_count (tetraEdgeBits B)

#print axioms tetrahedronCheck_of_realization
#print axioms tetra_bits_eq_count
#print axioms tetrahedronCheck_eq_count

end LittlewoodCylinders.Upper
