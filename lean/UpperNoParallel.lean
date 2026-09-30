import UpperParallel

/-! Elimination of parallel pairs in an eight-axis configuration. -/

namespace LittlewoodCylinders.Upper

open scoped RealInnerProductSpace
open LittlewoodCylinders.LineGeometry

theorem injective_three {ι : Type*} (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → ι) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_two]

theorem parallel_class_card_le_two (p u : Fin 8 → Space)
    (hu : ∀ i, u i ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1)
    (a b : Fin 8) (hab : cross (u a) (u b) ≠ 0) :
    (Finset.univ.filter fun i => cross (u a) (u i) = 0).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hcard)
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  let I : Fin 3 → Fin 8 := ![i, j, k]
  have hI : Function.Injective I := injective_three i j k hij hik hjk
  have hc (t : Fin 3) : cross (u a) (u (I t)) = 0 := by
    fin_cases t <;> simp [I, Matrix.cons_val_two, hi', hj', hk']
  apply no_three_parallel_with_transversal (fun t => p (I t)) (p b) (u a) (u b) (hu a) hab
  · intro s t hst
    have hh := hdist (I s) (I t) (fun heq => hst (hI heq))
    rw [lineDistance_replace_left _ _ _ (hu a) (hu (I s)) (hc s),
      lineDistance_replace_right _ _ _ (hu a) (hu (I t)) (hc t)] at hh
    exact hh
  · intro t
    have htb : I t ≠ b := by
      intro heq
      apply hab
      simpa only [heq] using hc t
    have hh := hdist (I t) b htb
    rw [lineDistance_replace_left _ _ _ (hu a) (hu (I t)) (hc t)] at hh
    exact hh

theorem common_normal_of_parallel_pair (p u : Fin 8 → Space)
    (hu : ∀ i, u i ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1)
    (a b : Fin 8) (hab : a ≠ b) (hcross : cross (u a) (u b) = 0) :
    ∃ n : Space, n ≠ 0 ∧ ∀ i, ⟪u i, n⟫ = 0 := by
  have hh := hdist a b hab
  rw [lineDistance_replace_right _ _ _ (hu a) (hu b) hcross] at hh
  obtain ⟨n, hn, hun, hthird⟩ := parallel_pair_common_normal (p a) (p b) (u a) (hu a) hh
  refine ⟨n, hn, ?_⟩
  intro i
  by_cases hc : cross (u a) (u i) = 0
  · rw [eq_smul_of_cross_eq_zero (hu a) hc, real_inner_smul_left, hun, mul_zero]
  · have hai : a ≠ i := by intro heq; subst i; exact hc (cross_self _)
    have hbi : b ≠ i := by intro heq; subst i; exact hc hcross
    apply hthird (p i) (u i) (hdist a i hai)
    have hh := hdist b i hbi
    rw [lineDistance_replace_left _ _ _ (hu a) (hu b) hcross] at hh
    exact hh

theorem no_parallel_in_eight (p u : Fin 8 → Space)
    (hu : ∀ i, u i ≠ 0)
    (hdist : ∀ i j, i ≠ j → lineDistance (p i) (u i) (p j) (u j) = 1) :
    ∀ a b, a ≠ b → cross (u a) (u b) ≠ 0 := by
  classical
  intro a b hab hcross
  obtain ⟨n, hn, hnormal⟩ := common_normal_of_parallel_pair p u hu hdist a b hab hcross
  by_cases hall : ∀ i, cross (u a) (u i) = 0
  · let I : Fin 4 → Fin 8 := fun i => ⟨i.val, by omega⟩
    have hI : Function.Injective I := by
      intro i j heq
      apply Fin.ext
      exact congrArg (fun t : Fin 8 => t.val) heq
    apply no_four_parallel_axes (fun i => p (I i)) (u a) (hu a)
    intro i j hij
    have hh := hdist (I i) (I j) (fun heq => hij (hI heq))
    rw [lineDistance_replace_left _ _ _ (hu a) (hu (I i)) (hall (I i)),
      lineDistance_replace_right _ _ _ (hu a) (hu (I j)) (hall (I j))] at hh
    exact hh
  · push Not at hall
    obtain ⟨c, hac⟩ := hall
    have hca : cross (u c) (u a) ≠ 0 := by
      intro hz
      apply hac
      rw [cross_reverse (u c) (u a), hz, neg_zero]
    have hcases (i : Fin 8) : cross (u a) (u i) = 0 ∨ cross (u c) (u i) = 0 := by
      by_contra hh
      push Not at hh
      have hne (j k : Fin 8) (h : cross (u j) (u k) ≠ 0) : j ≠ k := by
        intro heq; subst k; exact h (cross_self _)
      have ht := triple_ne_zero_of_unit_distances (p a) (p c) (p i) (u a) (u c) (u i)
        hac hh.1 hh.2 (hdist a c (hne a c hac))
        (hdist a i (hne a i hh.1)) (hdist c i (hne c i hh.2))
      exact ht (triple_zero_of_common_orthogonal hn (hnormal a) (hnormal c) (hnormal i))
    let A := Finset.univ.filter fun i => cross (u a) (u i) = 0
    let C := Finset.univ.filter fun i => cross (u c) (u i) = 0
    have hA : A.card ≤ 2 := parallel_class_card_le_two p u hu hdist a c hac
    have hC : C.card ≤ 2 := parallel_class_card_le_two p u hu hdist c a hca
    have hcover : (Finset.univ : Finset (Fin 8)) ⊆ A ∪ C := by
      intro i _
      rcases hcases i with hi | hi
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le A C)
    have hsize : (Finset.univ : Finset (Fin 8)).card = 8 := by decide
    omega

#print axioms no_parallel_in_eight

end LittlewoodCylinders.Upper
