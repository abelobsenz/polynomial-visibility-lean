import Visibility.RatioColumns
import Visibility.TightnessBound

/-!
# Density one of visible lattice points along a polynomial

`visibility_density_one` is the unconditional theorem for every nonzero integral
polynomial with at least two distinct complex roots. The zero polynomial is an
exception to the literal conjecture, formalized in `literal_conjecture_false`.
-/

namespace PolynomialVisibility

/-- Every nonzero integral polynomial with two distinct roots has visibility density one. -/
theorem visibility_density_one (F : Polynomial ℤ) (hF : F ≠ 0)
    (hroots : HasTwoDistinctRoots F) : HasVisibilityDensityOne F := by
  exact visibility_density_one_of_two_roots_and_reductions F hF hroots
    (gcdTight_of_ne_zero F hF) (sparseRatioColumns_of_two_roots F hF hroots)

end PolynomialVisibility
