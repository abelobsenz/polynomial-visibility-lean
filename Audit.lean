import Visibility

/- The public theorem must have exactly the intended hypotheses. -/
#check PolynomialVisibility.visibility_density_one
#print PolynomialVisibility.HasTwoDistinctRoots
#print PolynomialVisibility.Visible
#print PolynomialVisibility.HasVisibilityDensityOne

/- No project-specific mathematical axioms or admitted proofs may occur. -/
#print axioms PolynomialVisibility.visibility_density_one
#print axioms PolynomialVisibility.gcdTight_of_ne_zero
#print axioms PolynomialVisibility.polynomial_ratio_approximation
#print axioms PolynomialVisibility.naturalDensityZero_fixedRatioSet
#print axioms PolynomialVisibility.literal_conjecture_false

/- An expanded statement, independent of the two named hypothesis/conclusion wrappers. -/
example (F : Polynomial ℤ) (hF : F ≠ 0)
    (hroots : ∃ z w : ℂ, z ≠ w ∧ F.aeval z = 0 ∧ F.aeval w = 0) :
    Filter.Tendsto
      (fun N : ℕ => (PolynomialVisibility.visibleCount F N : ℝ) / (N : ℝ)^2)
      Filter.atTop (nhds 1) :=
  PolynomialVisibility.visibility_density_one F hF hroots
