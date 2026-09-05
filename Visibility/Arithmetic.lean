import Visibility.Definitions

/-!
# The exact arithmetic reduction

These lemmas make no asymptotic claims. The gcd and finite-ratio lemmas apply to
positive integer values of a polynomial, or to any other positive sequence.
-/

namespace PolynomialVisibility

/-- A smaller positive abscissa on the same rationally scaled curve. -/
def Blocker (F : Polynomial ℤ) (a h : ℕ) : Prop :=
  ∃ u : ℕ, 0 < u ∧ u < a ∧
    IsPositiveInteger ((h : ℚ) * ((F.eval (u : ℤ) : ℤ) : ℚ) /
      ((F.eval (a : ℤ) : ℤ) : ℚ))

/-- Visibility is exactly the absence of a smaller positive integral point. -/
theorem visible_iff_no_blocker (F : Polynomial ℤ) {a h : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hF : F.eval (a : ℤ) ≠ 0) :
    Visible F a h ↔ ¬ Blocker F a h := by
  have hFq : ((F.eval (a : ℤ) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hF
  constructor
  · rintro ⟨_, _, t, heq, hmin⟩ ⟨u, hu, hua, hint⟩
    have ht : (h : ℚ) / ((F.eval (a : ℤ) : ℤ) : ℚ) = t := by
      rw [heq, mul_div_cancel_right₀ _ hFq]
    have hint' : IsPositiveInteger (t * ((F.eval (u : ℤ) : ℤ) : ℚ)) := by
      convert hint using 1
      rw [← ht]
      ring
    exact (not_le_of_gt hua) (hmin u hu hint')
  · intro hn
    refine ⟨ha, hh, (h : ℚ) / ((F.eval (a : ℤ) : ℤ) : ℚ), ?_, ?_⟩
    · exact (div_mul_cancel₀ _ hFq).symm
    · intro u hu hint
      by_contra! hua
      apply hn
      refine ⟨u, hu, hua, ?_⟩
      convert hint using 1
      ring

/-- Cancelling the common divisor gives the exact integral-point condition. -/
theorem reduced_divisibility_iff {A B H : ℕ} (hA : 0 < A) :
    A / Nat.gcd A H ∣ B ↔ A ∣ H * B := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left A H)
    (Nat.gcd_pos_of_pos_left H hA), Nat.dvd_gcd_mul_iff_dvd_mul]

/-- Rational integrality and the elementary divisibility condition agree. -/
theorem positive_integer_ratio_iff {A B H : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) :
    IsPositiveInteger ((H : ℚ) * (B : ℚ) / (A : ℚ)) ↔ A ∣ H * B := by
  have hAq : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  constructor
  · rintro ⟨k, _, hk⟩
    refine ⟨k, ?_⟩
    have heq := (div_eq_iff hAq).mp hk
    exact_mod_cast heq.trans (mul_comm _ _)
  · rintro ⟨k, hk⟩
    have hkpos : 0 < k := by
      nlinarith [Nat.mul_pos hH hB]
    refine ⟨k, hkpos, ?_⟩
    apply (div_eq_iff hAq).mpr
    exact_mod_cast hk.trans (mul_comm _ _)

/-- A blocker with gcd at most `M` has one of finitely many value ratios. -/
theorem bounded_gcd_finite_ratio {A B H M : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B < A)
    (hdiv : A ∣ H * B) (hg : Nat.gcd A H ≤ M) :
    ∃ g r : ℕ, 1 ≤ g ∧ g ≤ M ∧ 1 ≤ r ∧ r < g ∧ g * B = r * A := by
  let g := Nat.gcd A H
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left H hA
  have hgA : g * (A / g) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A H)
  obtain ⟨r, hr⟩ := (reduced_divisibility_iff hA).mpr hdiv
  change B = (A / g) * r at hr
  have hrpos : 0 < r := by
    by_contra! hz
    simp only [Nat.le_zero] at hz
    simp [hz] at hr
    omega
  have hrg : r < g := by
    have : (A / g) * r < (A / g) * g := by
      simpa only [← hr, Nat.mul_comm (A / g) g, hgA] using hBA
    exact (Nat.mul_lt_mul_left (Nat.div_gcd_pos_of_pos_left H hA)).mp this
  refine ⟨g, r, hgpos, hg, hrpos, hrg, ?_⟩
  calc
    g * B = g * ((A / g) * r) := by rw [hr]
    _ = r * (g * (A / g)) := by ring
    _ = r * A := by rw [hgA]

/-- The finite list of fractions that occurs after a gcd cutoff. -/
def ratioSet (M : ℕ) : Finset ℚ :=
  (Finset.Icc 1 M).biUnion fun g =>
    (Finset.Ico 1 g).image fun r : ℕ => (r : ℚ) / (g : ℚ)

/-- The bounded-gcd reduction, expressed as membership in a finite set. -/
theorem ratio_mem_of_bounded_gcd {A B H M : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B < A)
    (hdiv : A ∣ H * B) (hg : Nat.gcd A H ≤ M) :
    (B : ℚ) / (A : ℚ) ∈ ratioSet M := by
  obtain ⟨g, r, hg1, hgM, hr1, hrg, heq⟩ :=
    bounded_gcd_finite_ratio hA hB hBA hdiv hg
  apply Finset.mem_biUnion.mpr
  refine ⟨g, Finset.mem_Icc.mpr ⟨hg1, hgM⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨r, Finset.mem_Ico.mpr ⟨hr1, hrg⟩, ?_⟩
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hAq : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  apply (div_eq_div_iff hgq hAq).mpr
  exact_mod_cast heq.symm.trans (mul_comm _ _)

/-- The divisibility criterion applied directly to positive polynomial values. -/
theorem polynomial_ratio_iff_reduced_divisibility
    (F : Polynomial ℤ) {a u h A B : ℕ}
    (hFa : F.eval (a : ℤ) = (A : ℤ))
    (hFu : F.eval (u : ℤ) = (B : ℤ))
    (hA : 0 < A) (hB : 0 < B) (hh : 0 < h) :
    IsPositiveInteger ((h : ℚ) * ((F.eval (u : ℤ) : ℤ) : ℚ) /
      ((F.eval (a : ℤ) : ℤ) : ℚ)) ↔ A / Nat.gcd A h ∣ B := by
  rw [hFa, hFu]
  simp only [Int.cast_natCast]
  rw [positive_integer_ratio_iff hA hB hh, reduced_divisibility_iff hA]

/-- A smaller positive polynomial value meeting the divisor test hides the point. -/
theorem not_visible_of_reduced_divisibility
    (F : Polynomial ℤ) {a u h A B : ℕ}
    (ha : 0 < a) (hu : 0 < u) (hua : u < a) (hh : 0 < h)
    (hFa : F.eval (a : ℤ) = (A : ℤ))
    (hFu : F.eval (u : ℤ) = (B : ℤ))
    (hA : 0 < A) (hB : 0 < B) (hdiv : A / Nat.gcd A h ∣ B) :
    ¬ Visible F a h := by
  have hF : F.eval (a : ℤ) ≠ 0 := by
    rw [hFa]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  intro hv
  apply (visible_iff_no_blocker F ha hh hF).mp hv
  refine ⟨u, hu, hua, ?_⟩
  exact (polynomial_ratio_iff_reduced_divisibility F hFa hFu hA hB hh).mpr hdiv

end PolynomialVisibility

namespace PolynomialVisibility

/-- Negating the polynomial only negates its rational scale. -/
theorem visible_neg_of_visible (F : Polynomial ℤ) {a h : ℕ}
    (hv : Visible F a h) : Visible (-F) a h := by
  obtain ⟨ha, hh, t, heq, hmin⟩ := hv
  refine ⟨ha, hh, -t, ?_, ?_⟩
  · simpa only [Polynomial.eval_neg, Int.cast_neg, neg_mul_neg] using heq
  · intro u hu hint
    apply hmin u hu
    simpa only [Polynomial.eval_neg, Int.cast_neg, neg_mul_neg] using hint

@[simp] theorem visible_neg_iff (F : Polynomial ℤ) (a h : ℕ) :
    Visible (-F) a h ↔ Visible F a h := by
  constructor
  · intro hv
    simpa only [neg_neg] using visible_neg_of_visible (-F) hv
  · exact visible_neg_of_visible F

@[simp] theorem visibleCount_neg (F : Polynomial ℤ) (N : ℕ) :
    visibleCount (-F) N = visibleCount F N := by
  classical
  unfold visibleCount
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => visible_neg_iff F p.1 p.2

@[simp] theorem visibility_density_one_neg_iff (F : Polynomial ℤ) :
    HasVisibilityDensityOne (-F) ↔ HasVisibilityDensityOne F := by
  simp [HasVisibilityDensityOne]

end PolynomialVisibility
