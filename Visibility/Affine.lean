import Mathlib

namespace PolynomialVisibility

open Polynomial

theorem coeff_shift_one_below (P : Polynomial ℝ) (n : ℕ)
    (hd : P.natDegree = n + 1) (γ : ℝ) :
    (P.comp (X + C γ)).coeff n =
      P.coeff n + (n + 1 : ℝ) * P.leadingCoeff * γ := by
  rw [comp, eval₂_eq_sum_range]
  simp only [hd, finset_sum_coeff, coeff_C_mul, coeff_X_add_C_pow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ i ∈ Finset.range n,
      P.coeff i * (γ ^ (i - n) * (i.choose n : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  rw [hzero]
  have hlc : P.coeff (n + 1) = P.leadingCoeff := by rw [← hd, coeff_natDegree]
  simp [hlc, Nat.choose_succ_self_right]
  ring

/-- The coefficient just below the leading term under an affine substitution. -/
theorem coeff_affine_one_below (P : Polynomial ℝ) (hd : 1 ≤ P.natDegree)
    (α γ : ℝ) :
    (P.comp (C α * X + C γ)).coeff (P.natDegree - 1) =
      α ^ (P.natDegree - 1) *
        (P.coeff (P.natDegree - 1) + (P.natDegree : ℝ) * P.leadingCoeff * γ) := by
  have haff : C α * X + C γ = (X + C γ).comp (C α * X) := by simp
  rw [haff, ← comp_assoc, comp_C_mul_X_coeff]
  have hd' : P.natDegree = (P.natDegree - 1) + 1 := by omega
  rw [coeff_shift_one_below P (P.natDegree - 1) hd' γ]
  have hcast : ((P.natDegree - 1 : ℕ) : ℝ) + 1 = (P.natDegree : ℝ) := by
    exact_mod_cast hd'.symm
  rw [hcast]
  ring

/-- Every proper positive ratio has a proper positive real `d`-th root. -/
theorem exists_positive_root_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {d : ℕ} (hd : 0 < d) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α ^ d = q := by
  let α : ℝ := q ^ ((d : ℝ)⁻¹)
  have hα0 : 0 < α := Real.rpow_pos_of_pos hq0 _
  have hpow : α ^ d = q := Real.rpow_inv_natCast_pow hq0.le hd.ne'
  refine ⟨α, hα0, ?_, hpow⟩
  by_contra! hge
  have hpowge : 1 ≤ α ^ d := one_le_pow₀ hge
  rw [hpow] at hpowge
  linarith

end PolynomialVisibility
