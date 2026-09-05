import Visibility.FixedRatio
import Visibility.DensityZero
import Visibility.Sign

namespace PolynomialVisibility

attribute [local instance] Classical.propDecidable

/-- Every fraction in the finite cutoff list lies strictly between zero and one. -/
theorem mem_ratioSet_bounds {M : ℕ} {q : ℚ} (hq : q ∈ ratioSet M) :
    0 < q ∧ q < 1 := by
  classical
  obtain ⟨g, hg, hrg⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrg
  obtain ⟨hg1, _⟩ := Finset.mem_Icc.mp hg
  obtain ⟨hr1, hrg⟩ := Finset.mem_Ico.mp hr
  have hgpos : (0 : ℚ) < g := by exact_mod_cast (show 0 < g by omega)
  constructor
  · apply div_pos _ hgpos
    exact_mod_cast (show 0 < r by omega)
  · apply (div_lt_one hgpos).mpr
    exact_mod_cast hrg

/-- A counted ratio column belongs to the finite union of fixed-ratio sets. -/
theorem ratioColumns_subset_union (F : Polynomial ℤ) (M N : ℕ) :
    ratioColumns F M N ⊆ (Finset.Icc 1 N).filter
      (fun a => a ∈ ⋃ q ∈ ratioSet M, fixedRatioSet F q) := by
  classical
  intro a ha
  obtain ⟨haN, u, hu, hua, hq⟩ := Finset.mem_filter.mp ha
  let q : ℚ := ((F.eval (u : ℤ) : ℤ) : ℚ) / ((F.eval (a : ℤ) : ℤ) : ℚ)
  have hqm : q ∈ ratioSet M := hq
  have hqne : q ≠ 0 := ne_of_gt (mem_ratioSet_bounds hqm).1
  have hFa : ((F.eval (a : ℤ) : ℤ) : ℚ) ≠ 0 := by
    intro hz
    apply hqne
    simp only [q, hz, div_zero]
  apply Finset.mem_filter.mpr
  refine ⟨haN, Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqm, ?_⟩⟩⟩
  refine ⟨u, hu, hua, ?_⟩
  exact (div_mul_cancel₀ _ hFa).symm

/-- Finite-ratio columns are sparse for polynomials with two distinct roots. -/
theorem sparseRatioColumns_of_positive_leadingCoeff
    (F : Polynomial ℤ) (hF : F ≠ 0) (htwo : HasTwoDistinctRoots F)
    (hlc : 0 < F.leadingCoeff) : SparseRatioColumns F := by
  classical
  intro M
  have hlimit := tendsto_Icc_finset_biUnion (ratioSet M) (fixedRatioSet F)
    (fun q hq => naturalDensityZero_fixedRatioSet F hF htwo hlc q
      (mem_ratioSet_bounds hq).1 (mem_ratioSet_bounds hq).2)
  apply squeeze_zero (fun N => by positivity) _ hlimit
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card (ratioColumns_subset_union F M N)

/-- The finite-ratio sparsity assertion is independent of the sign of the leading coefficient. -/
theorem sparseRatioColumns_of_two_roots
    (F : Polynomial ℤ) (hF : F ≠ 0) (htwo : HasTwoDistinctRoots F) :
    SparseRatioColumns F := by
  have hlc : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hF
  rcases lt_or_gt_of_ne hlc with hlcneg | hlcpos
  · apply (sparseRatioColumns_neg_iff F).mp
    apply sparseRatioColumns_of_positive_leadingCoeff (-F) (neg_ne_zero.mpr hF)
      ((hasTwoDistinctRoots_neg_iff F).mpr htwo)
    simpa only [Polynomial.leadingCoeff_neg, neg_pos] using hlcneg
  · exact sparseRatioColumns_of_positive_leadingCoeff F hF htwo hlcpos

end PolynomialVisibility
