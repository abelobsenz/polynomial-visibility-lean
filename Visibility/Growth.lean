/- Adapted from the existing local VDC/GrowthBound.lean development.
   No external VDC modules or assumptions are imported. -/
/-
# Existence of a growth threshold

Every integer polynomial of positive degree and positive leading coefficient
eventually has positive values exceeding every earlier positive-index value.

Route: pass to `P = F` over `ℝ`; the derivative `P'` has positive
leading coefficient, hence is eventually positive, so `P` is strictly
monotone on a ray `[x₀, ∞)`; since `P → ∞`, beyond some threshold the
values also exceed everything on the initial segment.
-/
import Visibility.Definitions

open Polynomial Filter

namespace PolynomialVisibility

/-- Polynomial values at natural abscissae, as integers. -/
def intValue (F : Polynomial ℤ) (a : ℕ) : ℤ := F.eval (a : ℤ)

/-- Beyond a record threshold values are positive and exceed every earlier value. -/
def IsGrowthBound (F : Polynomial ℤ) (A : ℕ) : Prop :=
  (∀ a : ℕ, A < a → 0 < intValue F a) ∧
  (∀ a b : ℕ, A < a → 1 ≤ b → b < a → intValue F b < intValue F a)

/-- A real polynomial with positive leading coefficient is eventually
positive. -/
theorem eventually_pos_of_leadingCoeff_pos (P : Polynomial ℝ)
    (hP : 0 < P.leadingCoeff) :
    ∀ᶠ x : ℝ in atTop, 0 < P.eval x := by
  by_cases hdeg : 0 < P.degree
  · exact (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP.le).eventually_gt_atTop 0
  · push_neg at hdeg
    have hdeg0 : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr hdeg
    have hC := Polynomial.eq_C_of_degree_le_zero hdeg
    filter_upwards with x
    conv_rhs => rw [hC]
    rw [eval_C]
    have : P.coeff 0 = P.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg0]
    rw [this]
    exact hP

/-- Every `F ∈ ℤ[x]`
of degree at least `1` with positive leading coefficient admits a growth
bound. -/
theorem exists_growthBound (F : Polynomial ℤ) (hdeg : 1 ≤ F.natDegree)
    (hlc : 0 < F.leadingCoeff) : ∃ nF : ℕ, IsGrowthBound F nF := by
  classical
  set P : Polynomial ℝ := F.map (Int.castRingHom ℝ) with hPdef
  have hlcne : (Int.castRingHom ℝ) F.leadingCoeff ≠ 0 := by
    simp only [eq_intCast, ne_eq, Int.cast_eq_zero]
    exact hlc.ne'
  have hPlc : P.leadingCoeff = (F.leadingCoeff : ℝ) :=
    leadingCoeff_map_of_leadingCoeff_ne_zero _ hlcne
  have hPlc0 : 0 < P.leadingCoeff := by
    rw [hPlc]; exact_mod_cast hlc
  have hPdeg : P.natDegree = F.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hlcne
  -- values of `P` at natural arguments are the values of `F`
  have hPeval : ∀ a : ℕ, P.eval (a : ℝ) = (intValue F a : ℝ) := by
    intro a
    rw [hPdef, intValue]
    rw [show ((a : ℕ) : ℝ) = (((a : ℕ) : ℤ) : ℝ) by push_cast; ring]
    rw [Polynomial.eval_intCast_map]
    simp
  -- the derivative has positive leading coefficient
  have hcoeffn : P.coeff F.natDegree = P.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hPdeg]
  have hc : P.derivative.coeff (F.natDegree - 1) =
      P.leadingCoeff * (F.natDegree : ℝ) := by
    have h := Polynomial.coeff_derivative P (F.natDegree - 1)
    rw [show F.natDegree - 1 + 1 = F.natDegree from by omega] at h
    rw [h, hcoeffn]
    congr 1
    ring_nf
    rw [show ((F.natDegree - 1 : ℕ) : ℝ) = (F.natDegree : ℝ) - 1 by
      push_cast [Nat.cast_sub hdeg]; ring]
    ring
  have hcpos : 0 < P.derivative.coeff (F.natDegree - 1) := by
    rw [hc]
    have : (0 : ℝ) < (F.natDegree : ℝ) := by exact_mod_cast hdeg
    positivity
  have hD'deg : P.derivative.natDegree = F.natDegree - 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hcpos.ne')
    calc P.derivative.natDegree ≤ P.natDegree - 1 :=
          natDegree_derivative_le P
      _ = F.natDegree - 1 := by rw [hPdeg]
  have hD'lc : 0 < P.derivative.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hD'deg]
    exact hcpos
  -- `P` is strictly monotone on a ray `[x₀, ∞)`
  obtain ⟨x₀, hx₀⟩ :=
    eventually_atTop.mp (eventually_pos_of_leadingCoeff_pos _ hD'lc)
  have hmono : StrictMonoOn (fun x => P.eval x) (Set.Ici x₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici x₀)
      (P.continuous.continuousOn) ?_
    intro x hx
    rw [Polynomial.deriv]
    rw [interior_Ici] at hx
    exact hx₀ x (le_of_lt hx)
  -- `P → ∞`, so beyond some threshold it beats the initial segment
  set M : ℕ := Nat.ceil x₀ with hMdef
  set B : ℕ := (Finset.Icc 1 M).sup fun b => (intValue F b).toNat with hBdef
  have hdegP : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos, hPdeg]
    omega
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp
    ((P.tendsto_atTop_of_leadingCoeff_nonneg hdegP hPlc0.le).eventually_gt_atTop
      (B : ℝ))
  refine ⟨max M (Nat.ceil x₁), ?_, ?_⟩
  · -- positivity beyond the threshold
    intro a ha
    have haM : Nat.ceil x₁ < a := lt_of_le_of_lt (le_max_right _ _) ha
    have hax₁ : x₁ ≤ (a : ℝ) := by
      calc x₁ ≤ (Nat.ceil x₁ : ℝ) := Nat.le_ceil x₁
        _ ≤ (a : ℝ) := by exact_mod_cast haM.le
    have hBa : (B : ℝ) < P.eval (a : ℝ) := hx₁ _ hax₁
    have : (0 : ℝ) < (intValue F a : ℝ) := by
      rw [← hPeval a]
      calc (0 : ℝ) ≤ (B : ℝ) := by positivity
        _ < P.eval (a : ℝ) := hBa
    exact_mod_cast this
  · -- strict domination of all earlier values
    intro a b ha hb1 hba
    have haM : Nat.ceil x₁ < a := lt_of_le_of_lt (le_max_right _ _) ha
    have hax₁ : x₁ ≤ (a : ℝ) := by
      calc x₁ ≤ (Nat.ceil x₁ : ℝ) := Nat.le_ceil x₁
        _ ≤ (a : ℝ) := by exact_mod_cast haM.le
    have hBa : (B : ℝ) < P.eval (a : ℝ) := hx₁ _ hax₁
    by_cases hbM : b ≤ M
    · -- `b` in the initial segment: `F(b) ≤ B < F(a)`
      have hbB : intValue F b ≤ (B : ℤ) := by
        have hmem : b ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hb1, hbM⟩
        have hsup : (intValue F b).toNat ≤ B :=
          Finset.le_sup (f := fun b => (intValue F b).toNat) hmem
        calc intValue F b ≤ ((intValue F b).toNat : ℤ) := Int.self_le_toNat _
          _ ≤ (B : ℤ) := by exact_mod_cast hsup
      have hBa' : (B : ℤ) < intValue F a := by
        have : (B : ℝ) < (intValue F a : ℝ) := by rw [← hPeval a]; exact hBa
        exact_mod_cast this
      omega
    · -- `b` beyond `M`: strict monotonicity on the ray
      push_neg at hbM
      have hbx₀ : x₀ ≤ (b : ℝ) := by
        calc x₀ ≤ (M : ℝ) := Nat.le_ceil x₀
          _ ≤ (b : ℝ) := by exact_mod_cast hbM.le
      have hax₀ : x₀ ≤ (a : ℝ) := by
        have hMa : M < a := lt_of_le_of_lt (le_max_left _ _) ha
        calc x₀ ≤ (M : ℝ) := Nat.le_ceil x₀
          _ ≤ (a : ℝ) := by exact_mod_cast hMa.le
      have hlt : P.eval (b : ℝ) < P.eval (a : ℝ) :=
        hmono hbx₀ hax₀ (by exact_mod_cast hba)
      have : (intValue F b : ℝ) < (intValue F a : ℝ) := by
        rw [← hPeval a, ← hPeval b]; exact hlt
      exact_mod_cast this

end PolynomialVisibility
