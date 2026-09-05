import Visibility.Arithmetic
import Visibility.Growth

/-!
# Counting reduction to two explicit asymptotic hypotheses

The final theorem in this file is conditional: it does not assert either of the
two asymptotic hypotheses for an arbitrary polynomial.
-/

namespace PolynomialVisibility

/-- Natural value, used only at positive polynomial values in the reduction. -/
def value (F : Polynomial ℤ) (a : ℕ) : ℕ := (F.eval (a : ℤ)).natAbs

noncomputable def invisibleCount (F : Polynomial ℤ) (N : ℕ) : ℕ := by
  classical
  exact ((square N).filter fun p => ¬ Visible F p.1 p.2).card

noncomputable def badGcdPoints (F : Polynomial ℤ) (M N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (square N).filter fun p => M < Nat.gcd (value F p.1) p.2

noncomputable def badGcdCount (F : Polynomial ℤ) (M N : ℕ) : ℕ :=
  (badGcdPoints F M N).card

/-- Columns containing a smaller abscissa with one of the bounded-denominator ratios. -/
noncomputable def ratioColumns (F : Polynomial ℤ) (M N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun a =>
    ∃ u : ℕ, 0 < u ∧ u < a ∧
      (((F.eval (u : ℤ) : ℤ) : ℚ) / ((F.eval (a : ℤ) : ℤ) : ℚ)) ∈ ratioSet M

/-- Quantified tightness of the gcd distribution in positive squares. -/
def GcdTight (F : Polynomial ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ N : ℕ in Filter.atTop,
    (badGcdCount F M N : ℝ) / (N : ℝ) ^ 2 < ε

/-- Every fixed finite set of nontrivial value ratios occupies density-zero columns. -/
def SparseRatioColumns (F : Polynomial ℤ) : Prop :=
  ∀ M : ℕ, Filter.Tendsto
    (fun N : ℕ => ((ratioColumns F M N).card : ℝ) / (N : ℝ))
    Filter.atTop (nhds 0)

/-- Past `A₀`, every value is positive and exceeds all earlier positive-index values. -/
def RecordAfter (F : Polynomial ℤ) (A₀ : ℕ) : Prop :=
  ∀ a : ℕ, A₀ < a → 0 < F.eval (a : ℤ) ∧
    ∀ u : ℕ, 0 < u → u < a → F.eval (u : ℤ) < F.eval (a : ℤ)

@[simp] theorem card_square (N : ℕ) : (square N).card = N ^ 2 := by
  simp [square, Finset.card_product, Nat.card_Icc, pow_two]

theorem count_partition (F : Polynomial ℤ) (N : ℕ) :
    visibleCount F N + invisibleCount F N = N ^ 2 := by
  classical
  rw [visibleCount, invisibleCount, Finset.card_filter_add_card_filter_not, card_square]

/-- Positive rational height at an earlier index forces a positive polynomial value. -/
theorem earlier_value_pos (F : Polynomial ℤ) {a u h : ℕ}
    (hh : 0 < h) (hFa : 0 < F.eval (a : ℤ))
    (hint : IsPositiveInteger ((h : ℚ) * ((F.eval (u : ℤ) : ℤ) : ℚ) /
      ((F.eval (a : ℤ) : ℤ) : ℚ))) : 0 < F.eval (u : ℤ) := by
  have hFaq : (0 : ℚ) < ((F.eval (a : ℤ) : ℤ) : ℚ) := by exact_mod_cast hFa
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  obtain ⟨k, hk, heq⟩ := hint
  have hpos : (0 : ℚ) < (h : ℚ) * ((F.eval (u : ℤ) : ℤ) : ℚ) /
      ((F.eval (a : ℤ) : ℤ) : ℚ) := by
    rw [heq]
    exact_mod_cast hk
  have huq := (mul_pos_iff_of_pos_left hhq).mp
    ((div_pos_iff_of_pos_right hFaq).mp hpos)
  exact_mod_cast huq

/-- Every late invisible point is in a sparse-ratio column or has large gcd. -/
theorem invisible_point_cover (F : Polynomial ℤ) {A₀ M N a h : ℕ}
    (hrecord : RecordAfter F A₀) (haN : a ∈ Finset.Icc 1 N)
    (hhN : h ∈ Finset.Icc 1 N) (ha : A₀ < a) (hinv : ¬ Visible F a h) :
    a ∈ ratioColumns F M N ∨ (a, h) ∈ badGcdPoints F M N := by
  classical
  have hap : 0 < a := (Finset.mem_Icc.mp haN).1
  have hhp : 0 < h := (Finset.mem_Icc.mp hhN).1
  by_cases hg : M < Nat.gcd (value F a) h
  · exact Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haN, hhN⟩, hg⟩)
  · have hg' : Nat.gcd (value F a) h ≤ M := Nat.le_of_not_gt hg
    have hFa := (hrecord a ha).1
    have hFne : F.eval (a : ℤ) ≠ 0 := ne_of_gt hFa
    have hblock : Blocker F a h := by
      by_contra hn
      exact hinv ((visible_iff_no_blocker F hap hhp hFne).mpr hn)
    obtain ⟨u, hup, hua, hint⟩ := hblock
    have hFu : 0 < F.eval (u : ℤ) := earlier_value_pos F hhp hFa hint
    have hFa' : F.eval (a : ℤ) = (value F a : ℤ) := by
      simp [value, abs_of_pos hFa]
    have hFu' : F.eval (u : ℤ) = (value F u : ℤ) := by
      simp [value, abs_of_pos hFu]
    have hA : 0 < value F a := by
      have : (0 : ℤ) < (value F a : ℤ) := hFa' ▸ hFa
      exact_mod_cast this
    have hB : 0 < value F u := by
      have : (0 : ℤ) < (value F u : ℤ) := hFu' ▸ hFu
      exact_mod_cast this
    have hBA : value F u < value F a := by
      have := (hrecord a ha).2 u hup hua
      rw [hFu', hFa'] at this
      exact_mod_cast this
    have hd : value F a ∣ h * value F u := by
      apply (reduced_divisibility_iff hA).mp
      exact (polynomial_ratio_iff_reduced_divisibility F hFa' hFu' hA hB hhp).mp hint
    have hr := ratio_mem_of_bounded_gcd hA hB hBA hd hg'
    left
    apply Finset.mem_filter.mpr
    refine ⟨haN, u, hup, hua, ?_⟩
    simpa only [hFa', hFu', Int.cast_natCast] using hr

/-- Exact finite-square estimate underlying the density argument. -/
theorem invisible_count_le (F : Polynomial ℤ) {A₀ M N : ℕ}
    (hrecord : RecordAfter F A₀) :
    invisibleCount F N ≤ A₀ * N + (ratioColumns F M N).card * N + badGcdCount F M N := by
  classical
  let early := (Finset.Icc 1 A₀) ×ˢ (Finset.Icc 1 N)
  let ratio := (ratioColumns F M N) ×ˢ (Finset.Icc 1 N)
  have hsub : (square N).filter (fun p => ¬ Visible F p.1 p.2) ⊆
      (early ∪ ratio) ∪ badGcdPoints F M N := by
    intro p hp
    obtain ⟨hpN, hinv⟩ := Finset.mem_filter.mp hp
    obtain ⟨haN, hhN⟩ := Finset.mem_product.mp hpN
    by_cases ha : p.1 ≤ A₀
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp haN).1, ha⟩, hhN⟩
    · rcases invisible_point_cover F hrecord haN hhN (Nat.lt_of_not_ge ha) hinv with hr | hg
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_product.mpr ⟨hr, hhN⟩
      · exact Finset.mem_union_right _ hg
  calc
    invisibleCount F N ≤ ((early ∪ ratio) ∪ badGcdPoints F M N).card := Finset.card_le_card hsub
    _ ≤ (early ∪ ratio).card + (badGcdPoints F M N).card := Finset.card_union_le _ _
    _ ≤ early.card + ratio.card + (badGcdPoints F M N).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = A₀ * N + (ratioColumns F M N).card * N + badGcdCount F M N := by
      simp [early, ratio, badGcdCount, Nat.card_Icc]

end PolynomialVisibility

namespace PolynomialVisibility

/-- Normalized form of the finite-square bound. -/
theorem invisible_density_le (F : Polynomial ℤ) {A₀ M N : ℕ}
    (hrecord : RecordAfter F A₀) (hN : 0 < N) :
    (invisibleCount F N : ℝ) / (N : ℝ) ^ 2 ≤
      (A₀ : ℝ) / (N : ℝ) + ((ratioColumns F M N).card : ℝ) / (N : ℝ) +
        (badGcdCount F M N : ℝ) / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc : (invisibleCount F N : ℝ) ≤
      (A₀ : ℝ) * (N : ℝ) + ((ratioColumns F M N).card : ℝ) * (N : ℝ) +
        (badGcdCount F M N : ℝ) := by exact_mod_cast invisible_count_le F hrecord
  calc
    (invisibleCount F N : ℝ) / (N : ℝ) ^ 2 ≤
      ((A₀ : ℝ) * (N : ℝ) + ((ratioColumns F M N).card : ℝ) * (N : ℝ) +
        (badGcdCount F M N : ℝ)) / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

/-- Tight gcd tails and sparse fixed-ratio columns imply invisible density zero. -/
theorem invisible_density_zero_of_reductions (F : Polynomial ℤ) {A₀ : ℕ}
    (hrecord : RecordAfter F A₀) (hgcd : GcdTight F) (hsparse : SparseRatioColumns F) :
    Filter.Tendsto (fun N : ℕ => (invisibleCount F N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun N => lt_of_lt_of_le hb (by positivity)
  · intro b hb
    obtain ⟨M, hM⟩ := hgcd (b / 3) (by positivity)
    have hearly : Filter.Tendsto (fun N : ℕ => (A₀ : ℝ) / (N : ℝ))
        Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have he : ∀ᶠ N : ℕ in Filter.atTop, (A₀ : ℝ) / (N : ℝ) < b / 3 :=
      (tendsto_order.mp hearly).2 (b / 3) (by positivity)
    have hr : ∀ᶠ N : ℕ in Filter.atTop,
        ((ratioColumns F M N).card : ℝ) / (N : ℝ) < b / 3 :=
      (tendsto_order.mp (hsparse M)).2 (b / 3) (by positivity)
    filter_upwards [hM, he, hr, Filter.eventually_gt_atTop 0] with N hMN heN hrN hN
    have hbound := invisible_density_le F (M := M) hrecord hN
    linarith

/-- Conditional density theorem: all remaining asymptotic assumptions are explicit. -/
theorem visibility_density_one_of_reductions (F : Polynomial ℤ) {A₀ : ℕ}
    (hrecord : RecordAfter F A₀) (hgcd : GcdTight F) (hsparse : SparseRatioColumns F) :
    HasVisibilityDensityOne F := by
  have hi := invisible_density_zero_of_reductions F hrecord hgcd hsparse
  have hv : Filter.Tendsto
      (fun N : ℕ => 1 - (invisibleCount F N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hi
  unfold HasVisibilityDensityOne
  simp only [sub_zero] at hv
  apply hv.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hc : (visibleCount F N : ℝ) + (invisibleCount F N : ℝ) = (N : ℝ) ^ 2 := by
    exact_mod_cast count_partition F N
  apply (eq_div_iff (pow_ne_zero 2 hNr)).mpr
  field_simp
  linarith

end PolynomialVisibility

namespace PolynomialVisibility

/-- Every nonconstant polynomial with positive leading coefficient has a record cutoff. -/
theorem exists_recordAfter (F : Polynomial ℤ) (hdeg : 1 ≤ F.natDegree)
    (hlc : 0 < F.leadingCoeff) : ∃ A₀ : ℕ, RecordAfter F A₀ := by
  obtain ⟨A₀, hpos, hrec⟩ := exists_growthBound F hdeg hlc
  exact ⟨A₀, fun a ha => ⟨hpos a ha, fun u hu hua => hrec a u ha hu hua⟩⟩

/-- The record assumption can be discharged by elementary polynomial growth. -/
theorem visibility_density_one_of_positive_leadingCoeff
    (F : Polynomial ℤ) (hdeg : 1 ≤ F.natDegree) (hlc : 0 < F.leadingCoeff)
    (hgcd : GcdTight F) (hsparse : SparseRatioColumns F) :
    HasVisibilityDensityOne F := by
  obtain ⟨A₀, hrecord⟩ := exists_recordAfter F hdeg hlc
  exact visibility_density_one_of_reductions F hrecord hgcd hsparse

end PolynomialVisibility
