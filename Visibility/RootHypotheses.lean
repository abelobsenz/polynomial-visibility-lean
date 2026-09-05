import Visibility.Arithmetic

namespace PolynomialVisibility

/-- Two distinct roots force degree at least two for a nonzero polynomial. -/
theorem two_le_natDegree_of_two_roots (F : Polynomial ℤ) (hF : F ≠ 0)
    (htwo : HasTwoDistinctRoots F) : 2 ≤ F.natDegree := by
  classical
  obtain ⟨z, w, hzw, hz, hw⟩ := htwo
  have hz' : z ∈ F.aroots ℂ := Polynomial.mem_aroots.mpr ⟨hF, hz⟩
  have hw' : w ∈ F.aroots ℂ := Polynomial.mem_aroots.mpr ⟨hF, hw⟩
  have hsub : ({z, w} : Finset ℂ) ⊆ (F.aroots ℂ).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Multiset.mem_toFinset.mpr hz'
    · exact Multiset.mem_toFinset.mpr hw'
  calc
    2 = ({z, w} : Finset ℂ).card := by simp [hzw]
    _ ≤ (F.aroots ℂ).toFinset.card := Finset.card_le_card hsub
    _ ≤ (F.aroots ℂ).card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := F.card_roots_map_le_natDegree

@[simp] theorem hasTwoDistinctRoots_neg_iff (F : Polynomial ℤ) :
    HasTwoDistinctRoots (-F) ↔ HasTwoDistinctRoots F := by
  simp [HasTwoDistinctRoots]

end PolynomialVisibility
