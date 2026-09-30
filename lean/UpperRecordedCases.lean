import UpperFiveData

namespace LittlewoodCylinders.Upper

/-- The sign data arise from a uniform unit-distance moment system. -/
def SignRealizable (E : Fin 8 → Fin 8 → ℤ) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ) : Prop :=
  ∃ u m : Fin 8 → Space,
    (∀ a b, contact u m a b = (E a b : ℝ) * ‖cross (u a) (u b)‖) ∧
    ∀ a b c, a < b → b < c → 0 < (χ a b c : ℝ) * triple (u a) (u b) (u c)

theorem all_recorded_polygon_cases_impossible :
    ∀ r ∈ polygonRecords, ¬ SignRealizable r.E r.χ := by
  rintro r hr ⟨u, m, hT, hχ⟩
  exact recorded_polygon_excluded r hr u m (uniform_of_sorted_signs u r.χ hχ) hT hχ

theorem all_recorded_five_cases_impossible :
    ∀ r ∈ fiveRecords, ¬ SignRealizable r.E r.χ := by
  rintro r hr ⟨u, m, hT, hχ⟩
  exact recorded_five_excluded r hr u m hT hχ

/-- Local exclusion of all 827 records. The missing global coverage theorem
must still show that every eight-axis configuration leads to one of these records. -/
theorem all_827_recorded_cases_impossible :
    polygonRecords.length + fiveRecords.length = 827 ∧
    (∀ r ∈ polygonRecords, ¬ SignRealizable r.E r.χ) ∧
    (∀ r ∈ fiveRecords, ¬ SignRealizable r.E r.χ) :=
  ⟨recorded_obstruction_count, all_recorded_polygon_cases_impossible,
    all_recorded_five_cases_impossible⟩

#print axioms all_827_recorded_cases_impossible

end LittlewoodCylinders.Upper
