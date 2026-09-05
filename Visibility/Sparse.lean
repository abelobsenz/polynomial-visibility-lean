import Mathlib

namespace PolynomialVisibility

open Filter

attribute [local instance] Classical.propDecidable

/-- Integer points approaching a line of irrational slope eventually avoid each fixed gap. -/
theorem irrational_fixed_gap_exclusion
    (α β : ℝ) (hα : Irrational α) (S : Set ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, n ∈ S →
      ∃ z : ℤ, |(z : ℝ) - (α * n + β)| < ε)
    (k : ℕ) (hk : 0 < k) :
    ∃ A : ℕ, ∀ n ≥ A, n ∈ S → n + k ∉ S := by
  let δ : ℝ := |α * k - (round (α * k) : ℝ)|
  have hδ : 0 < δ := by
    exact abs_pos.mpr (sub_ne_zero.mpr ((hα.mul_natCast (Nat.ne_of_gt hk)).ne_int _))
  obtain ⟨A, hA⟩ := happrox (δ / 3) (by positivity)
  refine ⟨A, ?_⟩
  intro n hn hnS hnkS
  obtain ⟨z, hz⟩ := hA n hn hnS
  obtain ⟨w, hw⟩ := hA (n + k) (by omega) hnkS
  have hmin : δ ≤ |α * k - ((w - z : ℤ) : ℝ)| := round_le _ _
  have hid : α * (k : ℝ) - ((w - z : ℤ) : ℝ) =
      ((z : ℝ) - (α * n + β)) - ((w : ℝ) - (α * (n + k) + β)) := by
    push_cast
    ring
  rw [hid] at hmin
  have htri := abs_sub ((z : ℝ) - (α * n + β))
    ((w : ℝ) - (α * (n + k) + β))
  push_cast at hw
  linarith

/-- A finite collection of forbidden gaps can be avoided past one common threshold. -/
theorem fixed_gap_exclusion_uniform
    (S : Set ℕ)
    (hgap : ∀ k : ℕ, 0 < k → ∃ A : ℕ, ∀ n ≥ A, n ∈ S → n + k ∉ S)
    (L : ℕ) :
    ∃ A : ℕ, ∀ n ≥ A, ∀ k : ℕ, 0 < k → k ≤ L → n ∈ S → n + k ∉ S := by
  induction L with
  | zero => exact ⟨0, by intros; omega⟩
  | succ L ih =>
      obtain ⟨A, hA⟩ := ih
      obtain ⟨B, hB⟩ := hgap (L + 1) (by omega)
      refine ⟨max A B, ?_⟩
      intro n hn k hk hkL hnS
      by_cases hk' : k ≤ L
      · exact hA n (le_trans (le_max_left _ _) hn) k hk hk' hnS
      · have : k = L + 1 := by omega
        subst k
        exact hB n (le_trans (le_max_right _ _) hn) hnS

end PolynomialVisibility

namespace PolynomialVisibility

attribute [local instance] Classical.propDecidable

/-- A set avoiding the first `L` gaps above `A` has at most one point in each block. -/
theorem gap_card_bound (S : Set ℕ) (A L N : ℕ) (hL : 0 < L)
    (hgap : ∀ n ≥ A, ∀ k : ℕ, 0 < k → k ≤ L → n ∈ S → n + k ∉ S) :
    ((Finset.range N).filter fun n => n ∈ S).card ≤ A + N / L + 1 := by
  classical
  let T := (Finset.range N).filter fun n => n ∈ S ∧ A ≤ n
  have hT : T.card ≤ N / L + 1 := by
    rw [← Finset.card_range (N / L + 1)]
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n / L)
    · intro n hn
      change n ∈ (Finset.range N).filter (fun n => n ∈ S ∧ A ≤ n) at hn
      change n / L ∈ Finset.range (N / L + 1)
      have hnN : n < N := (Finset.mem_filter.mp hn).1 |> Finset.mem_range.mp
      exact Finset.mem_range.mpr (by
        have := Nat.div_le_div_right (le_of_lt hnN) (c := L)
        omega)
    · intro a ha b hb hab
      change a ∈ (Finset.range N).filter (fun n => n ∈ S ∧ A ≤ n) at ha
      change b ∈ (Finset.range N).filter (fun n => n ∈ S ∧ A ≤ n) at hb
      change a / L = b / L at hab
      have haS : a ∈ S := (Finset.mem_filter.mp ha).2.1
      have hbS : b ∈ S := (Finset.mem_filter.mp hb).2.1
      have hAa : A ≤ a := (Finset.mem_filter.mp ha).2.2
      have hAb : A ≤ b := (Finset.mem_filter.mp hb).2.2
      have hma := Nat.mod_lt a hL
      have hmb := Nat.mod_lt b hL
      have hda := Nat.div_add_mod a L
      have hdb := Nat.div_add_mod b L
      rw [hab] at hda
      rcases lt_trichotomy a b with hab' | hab' | hab'
      · have hk : b - a ≤ L := by omega
        have hx := hgap a hAa (b - a) (by omega) hk haS
        rw [Nat.add_sub_of_le (le_of_lt hab')] at hx
        exact False.elim (hx hbS)
      · exact hab'
      · have hk : a - b ≤ L := by omega
        have hx := hgap b hAb (a - b) (by omega) hk hbS
        rw [Nat.add_sub_of_le (le_of_lt hab')] at hx
        exact False.elim (hx haS)
  have hsub : (Finset.range N).filter (fun n => n ∈ S) ⊆ (Finset.range A) ∪ T := by
    intro n hn
    have hnN := (Finset.mem_filter.mp hn).1
    have hnS := (Finset.mem_filter.mp hn).2
    by_cases hnA : n < A
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hnA)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hnS, by omega⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_range] at hcard
  omega

end PolynomialVisibility

namespace PolynomialVisibility

attribute [local instance] Classical.propDecidable

/-- Natural density zero, counted on the initial intervals `[0,N)`. -/
def NaturalDensityZero (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun N : ℕ =>
    (((Finset.range N).filter fun n => n ∈ S).card : ℝ) / N)
    Filter.atTop (nhds 0)

/-- Eventual exclusion of every fixed gap forces density zero. -/
theorem naturalDensityZero_of_fixed_gap_exclusion
    (S : Set ℕ)
    (hgap : ∀ k : ℕ, 0 < k → ∃ A : ℕ, ∀ n ≥ A, n ∈ S → n + k ∉ S) :
    NaturalDensityZero S := by
  rw [NaturalDensityZero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt ((2 : ℝ) / ε)
  have hLposR : 0 < (L : ℝ) := lt_trans (by positivity) hL
  have hLpos : 0 < L := by exact_mod_cast hLposR
  have hLtwo : 2 < ε * (L : ℝ) := by
    have := (div_lt_iff₀ hε).mp hL
    nlinarith
  obtain ⟨A, hA⟩ := fixed_gap_exclusion_uniform S hgap L
  obtain ⟨B, hB⟩ := exists_nat_gt (2 * ((A : ℝ) + 1) / ε)
  refine ⟨B, ?_⟩
  intro n hn
  have hnB : (B : ℝ) ≤ n := by exact_mod_cast hn
  have hnlarge : 2 * ((A : ℝ) + 1) < ε * (n : ℝ) := by
    have := (div_lt_iff₀ hε).mp hB
    nlinarith
  have hnpos : 0 < (n : ℝ) := by nlinarith [show (0 : ℝ) ≤ A by positivity]
  have hcount := gap_card_bound S A L n hLpos hA
  have hcountR : (((Finset.range n).filter fun a => a ∈ S).card : ℝ) ≤
      (A : ℝ) + ((n / L : ℕ) : ℝ) + 1 := by exact_mod_cast hcount
  have hdiv : ((n / L : ℕ) : ℝ) ≤ (n : ℝ) / (L : ℝ) := Nat.cast_div_le
  have hsmall : (n : ℝ) / (L : ℝ) < ε * n / 2 := by
    apply (div_lt_iff₀ hLposR).mpr
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply (div_lt_iff₀ hnpos).mpr
  nlinarith

/-- Integer points approaching an irrational affine line form a set of density zero. -/
theorem naturalDensityZero_of_irrational_approximation
    (α β : ℝ) (hα : Irrational α) (S : Set ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, n ∈ S →
      ∃ z : ℤ, |(z : ℝ) - (α * n + β)| < ε) :
    NaturalDensityZero S := by
  apply naturalDensityZero_of_fixed_gap_exclusion S
  intro k hk
  exact irrational_fixed_gap_exclusion α β hα S happrox k hk

end PolynomialVisibility

namespace PolynomialVisibility

/-- A rational affine line has a fixed positive separation from integer points off the line. -/
theorem rational_affine_separation (α β : ℚ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℤ,
      |(z : ℝ) - ((α : ℝ) * n + (β : ℝ))| < δ →
      (z : ℝ) = (α : ℝ) * n + (β : ℝ) := by
  let D : ℕ := α.den * β.den
  have ha : (α.den : ℝ) ≠ 0 := by exact_mod_cast α.den_nz
  have hb : (β.den : ℝ) ≠ 0 := by exact_mod_cast β.den_nz
  have hD : (0 : ℝ) < D := by
    dsimp [D]
    exact_mod_cast Nat.mul_pos α.den_pos β.den_pos
  refine ⟨(D : ℝ)⁻¹, by positivity, ?_⟩
  intro n z he
  let m : ℤ := (D : ℤ) * z - (β.den : ℤ) * α.num * n - (α.den : ℤ) * β.num
  have hid : (m : ℝ) = (D : ℝ) * ((z : ℝ) - ((α : ℝ) * n + (β : ℝ))) := by
    dsimp [m, D]
    push_cast
    rw [Rat.cast_def α, Rat.cast_def β]
    field_simp
    ring
  have hm : |(m : ℝ)| < 1 := by
    rw [hid, abs_mul, abs_of_pos hD]
    have := mul_lt_mul_of_pos_left he hD
    simpa only [mul_inv_cancel₀ (ne_of_gt hD)] using this
  have hmZ : |m| < 1 := by exact_mod_cast hm
  have hm0 : m = 0 := by
    have := abs_lt.mp hmZ
    omega
  rw [hm0, Int.cast_zero] at hid
  have := (mul_eq_zero.mp hid.symm).resolve_left (ne_of_gt hD)
  exact sub_eq_zero.mp this

/-- Shrinking errors from a rational affine line eventually vanish exactly. -/
theorem rational_approximation_eventually_exact
    (α β : ℚ) (S : Set ℕ) (f : ℕ → ℤ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, n ∈ S →
      |(f n : ℝ) - ((α : ℝ) * n + (β : ℝ))| < ε) :
    ∃ A : ℕ, ∀ n ≥ A, n ∈ S →
      (f n : ℝ) = (α : ℝ) * n + (β : ℝ) := by
  obtain ⟨δ, hδ, hsep⟩ := rational_affine_separation α β
  obtain ⟨A, hA⟩ := happrox δ hδ
  refine ⟨A, ?_⟩
  intro n hn hnS
  exact hsep (n : ℤ) (f n) (by simpa using hA n hn hnS)

end PolynomialVisibility

namespace PolynomialVisibility

/-- Every finite subset of the natural numbers has natural density zero. -/
theorem naturalDensityZero_of_finite (S : Set ℕ) (hS : S.Finite) :
    NaturalDensityZero S := by
  apply naturalDensityZero_of_fixed_gap_exclusion S
  intro k hk
  obtain ⟨B, hB⟩ := hS.bddAbove
  refine ⟨B + 1, ?_⟩
  intro n hn hnS
  have := hB hnS
  omega

/-- For a polynomial admitting no affine identity, a rational asymptote gives finitely many points. -/
theorem finite_of_rational_polynomial_approximation
    (P : Polynomial ℂ) (α β : ℚ) (q : ℂ)
    (hno : ¬ ∀ x : ℂ, P.eval ((α : ℂ) * x + (β : ℂ)) = q * P.eval x)
    (S : Set ℕ) (f : ℕ → ℤ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ, ∀ n ≥ A, n ∈ S →
      |(f n : ℝ) - ((α : ℝ) * n + (β : ℝ))| < ε)
    (heq : ∀ n ∈ S, P.eval (f n : ℂ) = q * P.eval (n : ℂ)) :
    S.Finite := by
  classical
  let Q : Polynomial ℂ :=
    P.comp (Polynomial.C (α : ℂ) * Polynomial.X + Polynomial.C (β : ℂ)) -
      Polynomial.C q * P
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hno
    intro x
    have hx := congrArg (fun R : Polynomial ℂ => R.eval x) hzero
    simpa [Q, sub_eq_zero] using hx
  have hroots : Set.Finite {n : ℕ | Q.IsRoot (n : ℂ)} := by
    apply (Polynomial.finite_setOf_isRoot hQ).preimage
    intro a ha b hb hab
    exact_mod_cast hab
  obtain ⟨A, hA⟩ := rational_approximation_eventually_exact α β S f happrox
  apply ((Finset.range A).finite_toSet.union hroots).subset
  intro n hnS
  by_cases hn : n < A
  · exact Or.inl (Finset.mem_range.mpr hn)
  · right
    have hreal := hA n (by omega) hnS
    have hrat : (f n : ℚ) = α * n + β := by exact_mod_cast hreal
    have hc : (f n : ℂ) = (α : ℂ) * n + (β : ℂ) := by exact_mod_cast hrat
    change Q.eval (n : ℂ) = 0
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [← hc, heq n hnS, sub_self]

end PolynomialVisibility
