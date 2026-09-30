import UpperSATCore

/-! Each local reason certifies an entire forbidden partial assignment.
Consequently the finite SAT argument needs no orbit-enumeration assumption. -/
namespace LittlewoodCylinders.Upper.SAT

open Sat

inductive Reason where
  | normalization
  | gp (a : Fin 8) (I : Fin 4 → Fin 8)
  | tetra (I : Fin 4 → Fin 8)
  | polygon (w : PolygonCertificate)
  | five (w : FiveCertificate)

def Reason.Valid (E : Fin 8 → Fin 8 → ℤ) (cl : List Literal) : Reason → Prop
  | .normalization => cl = [.pos (index 0 1 2)]
  | .gp a I => StrictMono I ∧ (∀ i, I i ≠ a) ∧
      (∀ i j, i < j → alternatingSign (partialOrientation cl) a (I i) (I j) ≠ 0) ∧
      gpCheck (partialOrientation cl) a (I 0) (I 1) (I 2) (I 3) = false
  | .tetra I => StrictMono I ∧ (∀ i, signedMinors (partialOrientation cl) I i ≠ 0) ∧
      tetraCountCheck (tetraEdgeBits (tetraMatrix E (partialOrientation cl) I)) = false
  | .polygon w => (PolygonRecord.mk 0 0 E (partialOrientation cl) w).Valid
  | .five w => (FiveRecord.mk 0 0 E (partialOrientation cl) w).Valid ∧
      ∀ i j k, i < j → j < k →
        alternatingSign (partialOrientation cl) (w.labels i) (w.labels j) (w.labels k) ≠ 0

instance (E : Fin 8 → Fin 8 → ℤ) (cl : List Literal) (r : Reason) :
    Decidable (r.Valid E cl) := by
  cases r <;> unfold Reason.Valid <;> infer_instance

theorem Reason.sound (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hfirst : χ 0 1 2 = 1)
    (hr : SignRealizable E χ) (hn : NecessarySignChecks E χ)
    (cl : List Literal) (r : Reason) (hv : r.Valid E cl) : (valuation χ).satisfies cl := by
  classical
  by_contra hf
  have ha := agrees_of_not_satisfies χ hu cl hf
  cases r with
  | normalization =>
    change cl = [.pos (index 0 1 2)] at hv
    subst cl
    have hh := neg_of_not_satisfies _ _ hf (.pos (index 0 1 2)) (by simp)
    exact hh ((valuation_index χ 0 1 2).mpr hfirst)
  | gp a I =>
    obtain ⟨hI, hi, hz, hbad⟩ := hv
    have heq (i j : Fin 4) (hij : i < j) :
        alternatingSign χ a (I i) (I j) =
        alternatingSign (partialOrientation cl) a (I i) (I j) :=
      ha.alternating a (I i) (I j) (hi i).symm (hi j).symm (hI hij).ne (hz i j hij)
    have hg := hn.1 a I hI hi
    unfold gpCheck at hg hbad
    rw [heq 0 1 (by decide), heq 2 3 (by decide), heq 0 2 (by decide),
      heq 1 3 (by decide), heq 0 3 (by decide), heq 1 2 (by decide)] at hg
    exact Bool.noConfusion (hg.symm.trans hbad)
  | tetra I =>
    obtain ⟨hI, hz, hbad⟩ := hv
    have heq := ha.minors I hI hz
    have hg := hn.2 I hI
    unfold tetraMatrix at hg hbad
    rw [heq] at hg
    exact Bool.noConfusion (hg.symm.trans hbad)
  | polygon w =>
    obtain ⟨hw, hI, hJ, hc, hd⟩ := hv
    have hcz (i : Fin 4) : signedMinors (partialOrientation cl) w.I i ≠ 0 := by
      rw [← hc]
      rcases hw.2.2.1 i with hh | hh <;> rw [hh] <;> decide
    have hdz (i : Fin 4) : signedMinors (partialOrientation cl) w.J i ≠ 0 := by
      rw [← hd]
      rcases hw.2.2.2.1 i with hh | hh <;> rw [hh] <;> decide
    have hc' : w.cSign = signedMinors χ w.I := hc.trans (ha.minors w.I hI hcz).symm
    have hd' : w.dSign = signedMinors χ w.J := hd.trans (ha.minors w.J hJ hdz).symm
    obtain ⟨u, m, hT, hχ⟩ := hr
    exact polygonRecord_sound ⟨0, 0, E, χ, w⟩ ⟨hw, hI, hJ, hc', hd'⟩ u m
      (uniform_of_sorted_signs u χ hχ) hT hχ
  | five w =>
    obtain ⟨⟨hi, hs, hg, hp, ht⟩, hz⟩ := hv
    have ht' (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
        w.signs i * w.signs j * w.signs k * fiveOrientation i j =
          alternatingSign χ (w.labels i) (w.labels j) (w.labels k) := by
      rw [ha.alternating (w.labels i) (w.labels j) (w.labels k)
        (fun h => hij.ne (hi h)) (fun h => (lt_trans hij hjk).ne (hi h))
        (fun h => hjk.ne (hi h)) (hz i j k hij hjk)]
      exact ht i j k hij hjk
    obtain ⟨u, m, hT, hχ⟩ := hr
    exact fiveRecord_sound ⟨0, 0, E, χ, w⟩ ⟨hi, hs, hg, hp, ht'⟩ u m hT hχ

/-- A certificate contains clauses and independently checkable local reasons. -/
def Valid (E : Fin 8 → Fin 8 → ℤ) (rs : List (List Literal × Reason)) : Prop :=
  ∀ cr ∈ rs, cr.2.Valid E cr.1

instance (E : Fin 8 → Fin 8 → ℤ) (rs : List (List Literal × Reason)) : Decidable (Valid E rs) :=
  inferInstanceAs (Decidable (∀ cr ∈ rs, cr.2.Valid E cr.1))

theorem satisfies_of_valid (E : Fin 8 → Fin 8 → ℤ) (rs : List (List Literal × Reason))
    (hv : Valid E rs) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hfirst : χ 0 1 2 = 1)
    (hr : SignRealizable E χ) (hn : NecessarySignChecks E χ) :
    (valuation χ).satisfies_fmla (rs.map Prod.fst) := by
  constructor
  intro cl hcl
  obtain ⟨cr, hcr, rfl⟩ := List.mem_map.mp hcl
  exact Reason.sound E χ hu hfirst hr hn cr.1 cr.2 (hv cr hcr)

#print axioms Reason.sound
#print axioms satisfies_of_valid

end LittlewoodCylinders.Upper.SAT
