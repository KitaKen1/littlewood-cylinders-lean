import LineGeometry

namespace LittlewoodCylinders.LineGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every one-dimensional affine subspace has a nonzero direction vector
and a base point. No closedness or coordinate assumptions are needed. -/
theorem exists_axis_parameters (L : AffineSubspace ℝ E)
    (hdim : Module.finrank ℝ L.direction = 1) :
    ∃ p u : E, u ≠ 0 ∧ L = affineLine p u := by
  have hL : L ≠ ⊥ := by
    intro hz
    rw [hz, AffineSubspace.direction_bot] at hdim
    simp at hdim
  obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot L).mpr hL
  have hdir : L.direction ≠ ⊥ := by
    intro hz
    rw [hz] at hdim
    simp at hdim
  obtain ⟨u, hu, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdir
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hu hune
  refine ⟨p, u, hune, ?_⟩
  rw [affineLine, ← hspan]
  exact (AffineSubspace.mk'_eq hp).symm

theorem exists_family_parameters {ι : Type*} (L : ι → AffineSubspace ℝ E)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1) :
    ∃ p u : ι → E, (∀ i, u i ≠ 0) ∧ ∀ i, L i = affineLine (p i) (u i) := by
  choose p u hu hL using fun i => exists_axis_parameters (L i) (hdim i)
  exact ⟨p, u, hu, hL⟩

#print axioms exists_family_parameters

end LittlewoodCylinders.LineGeometry
