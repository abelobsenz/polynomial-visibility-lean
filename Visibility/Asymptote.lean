import Visibility.Growth
import Visibility.Sparse
import Visibility.Affine

open Polynomial Filter

namespace PolynomialVisibility

/-- Every real polynomial of positive degree and positive leading coefficient is
strictly increasing on some terminal interval. -/
theorem real_polynomial_eventually_strictMono
    (P : Polynomial ℝ) (hdeg : 1 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) :
    ∃ x₀ : ℝ, StrictMonoOn P.eval (Set.Ici x₀) := by
  have hc : P.derivative.coeff (P.natDegree - 1) =
      P.leadingCoeff * (P.natDegree : ℝ) := by
    rw [Polynomial.coeff_derivative,
      show P.natDegree - 1 + 1 = P.natDegree by omega, Polynomial.coeff_natDegree]
    rw [Nat.cast_sub hdeg]
    push_cast
    ring
  have hcpos : 0 < P.derivative.coeff (P.natDegree - 1) := by
    rw [hc]
    have : (0 : ℝ) < P.natDegree := by exact_mod_cast (show 0 < P.natDegree by omega)
    positivity
  have hd : P.derivative.natDegree = P.natDegree - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_derivative_le P) (ne_of_gt hcpos)
  have hlcd : 0 < P.derivative.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hd]
    exact hcpos
  obtain ⟨x₀, hx₀⟩ :=
    eventually_atTop.mp (eventually_pos_of_leadingCoeff_pos P.derivative hlcd)
  refine ⟨x₀, ?_⟩
  refine strictMonoOn_of_deriv_pos (convex_Ici x₀) P.continuous.continuousOn ?_
  intro x hx
  rw [Polynomial.deriv]
  rw [interior_Ici] at hx
  exact hx₀ x (le_of_lt hx)

/-- Polynomial barriers around an affine line trap all positive integer solutions.
Only barriers with each fixed positive error are needed, rather than a quantitative
error estimate. -/
theorem approximation_of_polynomial_barriers
    (P : Polynomial ℝ) (hdeg : 1 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    (α β q : ℝ) (hα : 0 < α) (hq : 0 < q)
    (hbarrier : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      P.eval (α * x + β - ε) < q * P.eval x ∧
      q * P.eval x < P.eval (α * x + β + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, ∀ u : ℕ,
      P.eval (u : ℝ) = q * P.eval (n : ℝ) →
      |(u : ℝ) - (α * n + β)| < ε := by
  obtain ⟨x₀, hmono⟩ := real_polynomial_eventually_strictMono P hdeg hlc
  let M : ℕ := Nat.ceil x₀
  obtain ⟨B, hB⟩ :=
    ((Finset.range (M + 1)).finite_toSet.image (fun n : ℕ => P.eval (n : ℝ))).bddAbove
  have hBP : ∀ u : ℕ, u ≤ M → P.eval (u : ℝ) ≤ B := by
    intro u hu
    apply hB
    exact ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
  have hPtop : Tendsto P.eval atTop atTop := by
    apply P.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [← natDegree_pos_iff_degree_pos]
      omega
    · exact hlc.le
  have hQtop : Tendsto (fun x : ℝ => q * P.eval x) atTop atTop :=
    hPtop.const_mul_atTop hq
  intro ε hε
  have hLtop : Tendsto (fun x : ℝ => α * x + β - ε) atTop atTop := by
    simpa [sub_eq_add_neg, add_assoc] using
      (tendsto_atTop_add_const_right atTop (β - ε) (tendsto_id.const_mul_atTop hα))
  obtain ⟨C, hC⟩ := eventually_atTop.mp
    ((hbarrier ε hε).and ((hQtop.eventually_gt_atTop B).and
      (hLtop.eventually_ge_atTop x₀)))
  refine ⟨Nat.ceil C, ?_⟩
  intro n hn u heq
  have hnC : C ≤ (n : ℝ) :=
    (Nat.le_ceil C).trans (by exact_mod_cast hn)
  obtain ⟨⟨hleft, hright⟩, hnB, hnL⟩ := hC (n : ℝ) hnC
  have huM : M < u := by
    by_contra! h
    have := hBP u h
    rw [heq] at this
    linarith
  have hu : (u : ℝ) ∈ Set.Ici x₀ := by
    change x₀ ≤ (u : ℝ)
    exact (Nat.le_ceil x₀).trans (by exact_mod_cast huM.le)
  have hLo : α * (n : ℝ) + β - ε ∈ Set.Ici x₀ := hnL
  have hHi : α * (n : ℝ) + β + ε ∈ Set.Ici x₀ := by
    change x₀ ≤ _
    linarith
  have huL : α * (n : ℝ) + β - ε < (u : ℝ) := by
    by_contra! h
    have := hmono.monotoneOn hu hLo h
    rw [heq] at this
    linarith
  have huH : (u : ℝ) < α * (n : ℝ) + β + ε := by
    by_contra! h
    have := hmono.monotoneOn hHi hu h
    rw [heq] at this
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end PolynomialVisibility

namespace PolynomialVisibility

/-- Cancellation of the leading term under the matching affine dilation. -/
theorem affine_difference_data (P : Polynomial ℝ) (hd : 1 ≤ P.natDegree)
    (α γ : ℝ) (hα : α ≠ 0) :
    let H := P.comp (C α * X + C γ) - C (α ^ P.natDegree) * P
    H.natDegree ≤ P.natDegree - 1 ∧
    H.coeff (P.natDegree - 1) = α ^ (P.natDegree - 1) *
      (P.coeff (P.natDegree - 1) + (P.natDegree : ℝ) * P.leadingCoeff * γ -
        α * P.coeff (P.natDegree - 1)) := by
  let L : Polynomial ℝ := C α * X + C γ
  have hL : L.natDegree = 1 := by simp [L, hα]
  have hLl : L.leadingCoeff = α := by
    rw [leadingCoeff, hL]
    simp [L]
  have hcomp : (P.comp L).natDegree = P.natDegree := by
    rw [natDegree_comp, hL, mul_one]
  have htop : (P.comp L).coeff P.natDegree = P.leadingCoeff * α ^ P.natDegree := by
    have h := coeff_comp_degree_mul_degree (p := P) (q := L) (by omega)
    simpa [hL, hLl] using h
  have hpow : α ^ P.natDegree = α ^ (P.natDegree - 1) * α := by
    rw [← pow_succ]
    congr 1
    omega
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases hnd : n = P.natDegree
    · subst n
      rw [coeff_sub, htop, coeff_C_mul, coeff_natDegree]
      ring
    · have hlt : P.natDegree < n := by omega
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by
          change (P.comp L).natDegree < n
          rw [hcomp]
          exact hlt),
        coeff_C_mul, coeff_eq_zero_of_natDegree_lt hlt]
      ring
  · rw [coeff_sub, coeff_C_mul, coeff_affine_one_below P hd, hpow]
    ring

/-- Every sufficiently large solution to a fixed ratio lies arbitrarily close to
its uniquely determined affine asymptote. -/
theorem polynomial_ratio_approximation
    (P : Polynomial ℝ) (hd : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    (α : ℝ) (hα : 0 < α) :
    let β := P.coeff (P.natDegree - 1) * (α - 1) /
      ((P.natDegree : ℝ) * P.leadingCoeff)
    ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, ∀ u : ℕ,
      P.eval (u : ℝ) = α ^ P.natDegree * P.eval (n : ℝ) →
      |(u : ℝ) - (α * n + β)| < ε := by
  let β := P.coeff (P.natDegree - 1) * (α - 1) /
      ((P.natDegree : ℝ) * P.leadingCoeff)
  have hdpos : (0 : ℝ) < P.natDegree := by exact_mod_cast (show 0 < P.natDegree by omega)
  have hscale : 0 < α ^ (P.natDegree - 1) * (P.natDegree : ℝ) * P.leadingCoeff := by
    positivity
  have hcoef (δ : ℝ) :
      (P.comp (C α * X + C (β + δ)) - C (α ^ P.natDegree) * P).coeff
        (P.natDegree - 1) =
      α ^ (P.natDegree - 1) * (P.natDegree : ℝ) * P.leadingCoeff * δ := by
    rw [(affine_difference_data P (by omega) α (β + δ) hα.ne').2]
    dsimp [β]
    field_simp
    ring
  apply approximation_of_polynomial_barriers P (by omega) hlc α β (α ^ P.natDegree) hα (by positivity)
  intro ε hε
  let Hplus := P.comp (C α * X + C (β + ε)) - C (α ^ P.natDegree) * P
  let Hminus := P.comp (C α * X + C (β + -ε)) - C (α ^ P.natDegree) * P
  have hpcoeff : 0 < Hplus.coeff (P.natDegree - 1) := by
    rw [hcoef]
    exact mul_pos hscale hε
  have hmcoeff : 0 < (-Hminus).coeff (P.natDegree - 1) := by
    rw [coeff_neg, hcoef]
    nlinarith
  have hpdeg : Hplus.natDegree = P.natDegree - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (affine_difference_data P (by omega) α (β + ε) hα.ne').1 hpcoeff.ne'
  have hmdeg : (-Hminus).natDegree = P.natDegree - 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ hmcoeff.ne'
    rw [natDegree_neg]
    exact (affine_difference_data P (by omega) α (β + -ε) hα.ne').1
  have hplc : 0 < Hplus.leadingCoeff := by
    rw [leadingCoeff, hpdeg]
    exact hpcoeff
  have hmlc : 0 < (-Hminus).leadingCoeff := by
    rw [leadingCoeff, hmdeg]
    exact hmcoeff
  filter_upwards [eventually_pos_of_leadingCoeff_pos Hplus hplc,
    eventually_pos_of_leadingCoeff_pos (-Hminus) hmlc] with x hp hm
  simp only [Hplus, Hminus, eval_sub, eval_comp, eval_add, eval_mul, eval_C,
    eval_X, eval_neg] at hp hm
  simp only [← add_assoc, ← sub_eq_add_neg, ← add_sub_assoc] at hp hm
  constructor <;> linarith

end PolynomialVisibility
