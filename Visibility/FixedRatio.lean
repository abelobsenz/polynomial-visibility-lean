import Visibility.Asymptote
import Visibility.Rigidity
import Visibility.RootHypotheses
import Visibility.Sparse

namespace PolynomialVisibility

/-- Abscissae with a smaller positive-index value in a fixed rational ratio. -/
def fixedRatioSet (F : Polynomial ℤ) (q : ℚ) : Set ℕ :=
  {n | ∃ u : ℕ, 0 < u ∧ u < n ∧
    ((F.eval (u : ℤ) : ℤ) : ℚ) = q * ((F.eval (n : ℤ) : ℤ) : ℚ)}

/-- A proper fixed value ratio occurs only in density-zero columns. -/
theorem naturalDensityZero_fixedRatioSet
    (F : Polynomial ℤ) (hF : F ≠ 0) (htwo : HasTwoDistinctRoots F)
    (hlc : 0 < F.leadingCoeff) (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    NaturalDensityZero (fixedRatioSet F q) := by
  classical
  let P : Polynomial ℝ := F.map (Int.castRingHom ℝ)
  let C : Polynomial ℂ := F.map (Int.castRingHom ℂ)
  have hlcne : (Int.castRingHom ℝ) F.leadingCoeff ≠ 0 := by
    change (F.leadingCoeff : ℝ) ≠ 0
    exact_mod_cast hlc.ne'
  have hPlc : P.leadingCoeff = (F.leadingCoeff : ℝ) :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlcne
  have hPdeg : P.natDegree = F.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlcne
  have hPlc0 : 0 < P.leadingCoeff := by rw [hPlc]; exact_mod_cast hlc
  have hdeg : 2 ≤ P.natDegree := by
    rw [hPdeg]
    exact two_le_natDegree_of_two_roots F hF htwo
  have hPeval : ∀ n : ℕ, P.eval (n : ℝ) = ((F.eval (n : ℤ) : ℤ) : ℝ) := by
    intro n
    simp [P, Polynomial.eval_map]
  have hCeval : ∀ n : ℕ, C.eval (n : ℂ) = ((F.eval (n : ℤ) : ℤ) : ℂ) := by
    intro n
    simp [C, Polynomial.eval_map]
  have hwitness : ∀ n : ℕ, ∃ u : ℕ, n ∈ fixedRatioSet F q →
      0 < u ∧ u < n ∧
      ((F.eval (u : ℤ) : ℤ) : ℚ) = q * ((F.eval (n : ℤ) : ℤ) : ℚ) := by
    intro n
    by_cases hn : n ∈ fixedRatioSet F q
    · obtain ⟨u, hu⟩ := hn
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => (hn h).elim⟩
  choose f hf using hwitness
  obtain ⟨α, hα0, hα1, hαpow⟩ := exists_positive_root_lt_one
    (show (0 : ℝ) < q by exact_mod_cast hq0)
    (show (q : ℝ) < 1 by exact_mod_cast hq1)
    (show 0 < P.natDegree by omega)
  let β := P.coeff (P.natDegree - 1) * (α - 1) /
    ((P.natDegree : ℝ) * P.leadingCoeff)
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A,
      n ∈ fixedRatioSet F q → |(f n : ℝ) - (α * n + β)| < ε := by
    intro ε hε
    obtain ⟨A, hA⟩ := polynomial_ratio_approximation P hdeg hPlc0 α hα0 ε hε
    refine ⟨A, ?_⟩
    intro n hn hnS
    apply hA n hn (f n)
    rw [hαpow, hPeval, hPeval]
    exact_mod_cast (hf n hnS).2.2
  by_cases hirr : Irrational α
  · apply naturalDensityZero_of_irrational_approximation α β hirr
    intro ε hε
    obtain ⟨A, hA⟩ := happrox ε hε
    refine ⟨A, ?_⟩
    intro n hn hnS
    exact ⟨(f n : ℤ), by simpa only [Int.cast_natCast] using hA n hn hnS⟩
  · obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hirr
    let b : ℚ := (F.coeff (F.natDegree - 1) : ℚ) * (r - 1) /
      ((F.natDegree : ℚ) * (F.leadingCoeff : ℚ))
    have hb : (b : ℝ) = β := by
      simp [b, β, hPdeg, hPlc, P, hr, Polynomial.coeff_map]
    have hC : C ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hF
    obtain ⟨z, w, hzw, hz, hw⟩ := htwo
    have hzC : C.IsRoot z := by
      simpa only [C, Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.aeval_def] using hz
    have hwC : C.IsRoot w := by
      simpa only [C, Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.aeval_def] using hw
    have hrC : (α : ℂ) = (r : ℂ) := by rw [hr]; norm_cast
    have hno : ¬ ∀ x : ℂ, C.eval ((r : ℂ) * x + (b : ℂ)) = (q : ℂ) * C.eval x := by
      simpa only [hrC] using
        no_affine_contraction_identity C hC z w hzw hzC hwC α (b : ℂ) (q : ℂ) hα0 hα1
    apply naturalDensityZero_of_finite
    apply finite_of_rational_polynomial_approximation C r b (q : ℂ) hno
      (fixedRatioSet F q) (fun n => (f n : ℤ))
    · intro ε hε
      obtain ⟨A, hA⟩ := happrox ε hε
      refine ⟨A, ?_⟩
      intro n hn hnS
      simpa only [Int.cast_natCast, hr, hb] using hA n hn hnS
    · intro n hnS
      simp only [Int.cast_natCast]
      rw [hCeval, hCeval]
      exact_mod_cast (hf n hnS).2.2

end PolynomialVisibility
