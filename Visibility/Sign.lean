import Visibility.Density
import Visibility.RootHypotheses

namespace PolynomialVisibility

@[simp] theorem value_neg (F : Polynomial ℤ) (a : ℕ) : value (-F) a = value F a := by
  simp [value]

@[simp] theorem badGcdPoints_neg (F : Polynomial ℤ) (M N : ℕ) :
    badGcdPoints (-F) M N = badGcdPoints F M N := by
  classical
  ext p
  simp [badGcdPoints]

@[simp] theorem badGcdCount_neg (F : Polynomial ℤ) (M N : ℕ) :
    badGcdCount (-F) M N = badGcdCount F M N := by
  simp [badGcdCount]

@[simp] theorem ratioColumns_neg (F : Polynomial ℤ) (M N : ℕ) :
    ratioColumns (-F) M N = ratioColumns F M N := by
  classical
  ext a
  simp [ratioColumns]

@[simp] theorem gcdTight_neg_iff (F : Polynomial ℤ) : GcdTight (-F) ↔ GcdTight F := by
  simp [GcdTight]

@[simp] theorem sparseRatioColumns_neg_iff (F : Polynomial ℤ) :
    SparseRatioColumns (-F) ↔ SparseRatioColumns F := by
  simp [SparseRatioColumns]

/-- Sign-independent assembly; the two number-theoretic density inputs are explicit. -/
theorem visibility_density_one_of_two_roots_and_reductions
    (F : Polynomial ℤ) (hF : F ≠ 0) (htwo : HasTwoDistinctRoots F)
    (hgcd : GcdTight F) (hsparse : SparseRatioColumns F) :
    HasVisibilityDensityOne F := by
  have hdeg : 1 ≤ F.natDegree := by
    have := two_le_natDegree_of_two_roots F hF htwo
    omega
  have hlc : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hF
  rcases lt_or_gt_of_ne hlc with hlcneg | hlcpos
  · apply (visibility_density_one_neg_iff F).mp
    apply visibility_density_one_of_positive_leadingCoeff (-F)
    · simpa only [Polynomial.natDegree_neg] using hdeg
    · simpa only [Polynomial.leadingCoeff_neg, neg_pos] using hlcneg
    · exact (gcdTight_neg_iff F).mpr hgcd
    · exact (sparseRatioColumns_neg_iff F).mpr hsparse
  · exact visibility_density_one_of_positive_leadingCoeff F hdeg hlcpos hgcd hsparse

end PolynomialVisibility
