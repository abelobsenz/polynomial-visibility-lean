import Visibility.Tightness
import Visibility.Density

namespace PolynomialVisibility

open Finset

/-- Zero-based indices for the positive square, convenient for exact counts of
    multiples. -/
noncomputable def rangeBadPoints (F : Polynomial ℤ) (M N : ℕ) : Finset (ℕ × ℕ) :=
  ((range N) ×ˢ (range N)).filter fun z =>
    M < Nat.gcd (F.eval ((z.1 + 1 : ℕ) : ℤ)).natAbs (z.2 + 1)

/-- Simultaneous divisibility of the polynomial value and the height. -/
noncomputable def primePair (F : Polynomial ℤ) (N p : ℕ) : Finset (ℕ × ℕ) :=
  ((range N).filter (fun a => p ∣ (F.eval ((a + 1 : ℕ) : ℤ)).natAbs)) ×ˢ
    ((range N).filter (fun h => p ∣ h + 1))

/-- A high prime power in the height. -/
noncomputable def powerPair (N p E : ℕ) : Finset (ℕ × ℕ) :=
  (range N) ×ˢ ((range N).filter (fun h => p ^ E ∣ h + 1))

/-- The exact count of a prime-pair event is bounded by the polynomial degree
    times the elementary counts in residue classes. -/
theorem card_primePair_le (F : Polynomial ℤ) (N p : ℕ) [Fact p.Prime]
    (hF : reduction F p ≠ 0) :
    (primePair F N p).card ≤ F.natDegree * (N / p + 1) * (N / p) := by
  unfold primePair
  rw [card_product, Nat.card_multiples]
  have hc := Nat.mul_le_mul_right (N / p) (card_prime_divides_values_le F N p hF)
  simpa only [Nat.mul_comm (N / p + 1) F.natDegree] using hc

/-- The prime-power event is bounded uniformly over primes. -/
theorem card_powerPair_le (N p E : ℕ) (hp : p.Prime) :
    (powerPair N p E).card ≤ N * (N / 2 ^ E) := by
  unfold powerPair
  rw [card_product, card_range, Nat.card_multiples]
  exact Nat.mul_le_mul_left N (Nat.div_le_div_left (Nat.pow_le_pow_left hp.two_le E) (by positivity))

/-- Explicit finite union bound for a large gcd. -/
theorem card_rangeBadPoints_le_sum (F : Polynomial ℤ) (N K E : ℕ)
    (hF : ∀ p : ℕ, p.Prime → K < p → reduction F p ≠ 0) :
    (rangeBadPoints F (K.factorial ^ E) N).card ≤
      (∑ p ∈ (Ioo K (N + 1)).filter Nat.Prime,
        F.natDegree * (N / p + 1) * (N / p)) +
      (K + 1) * (N * (N / 2 ^ E)) := by
  classical
  let L := (Ioo K (N + 1)).filter Nat.Prime
  let S := (range (K + 1)).filter Nat.Prime
  have hsubset : rangeBadPoints F (K.factorial ^ E) N ⊆
      (L.biUnion (primePair F N)) ∪ (S.biUnion (fun p => powerPair N p E)) := by
    intro z hz
    obtain ⟨hzsquare, hzlarge⟩ := mem_filter.mp hz
    obtain ⟨haN, hhN⟩ := mem_product.mp hzsquare
    have he := large_gcd_has_prime_exception (Nat.succ_pos z.2) hzlarge
    rcases he with ⟨p, hp, hpK, hpa, hph⟩ | ⟨p, hp, hpK, hph⟩
    · apply mem_union.mpr
      left
      apply mem_biUnion.mpr
      have hpN : p ≤ N :=
        (Nat.le_of_dvd (Nat.succ_pos z.2) hph).trans
          (Nat.succ_le_of_lt (mem_range.mp hhN))
      refine ⟨p, mem_filter.mpr ⟨mem_Ioo.mpr ⟨hpK, Nat.lt_succ_of_le hpN⟩, hp⟩, ?_⟩
      exact mem_product.mpr ⟨mem_filter.mpr ⟨haN, hpa⟩, mem_filter.mpr ⟨hhN, hph⟩⟩
    · apply mem_union.mpr
      right
      apply mem_biUnion.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hpK), hp⟩, ?_⟩
      exact mem_product.mpr ⟨haN, mem_filter.mpr ⟨hhN, hph⟩⟩
  calc
    (rangeBadPoints F (K.factorial ^ E) N).card ≤
        (L.biUnion (primePair F N)).card +
          (S.biUnion (fun p => powerPair N p E)).card :=
      (card_le_card hsubset).trans (card_union_le _ _)
    _ ≤ (∑ p ∈ L, (primePair F N p).card) +
        ∑ p ∈ S, (powerPair N p E).card :=
      Nat.add_le_add card_biUnion_le card_biUnion_le
    _ ≤ (∑ p ∈ L, F.natDegree * (N / p + 1) * (N / p)) +
        ∑ _p ∈ S, N * (N / 2 ^ E) := by
      apply Nat.add_le_add
      · apply sum_le_sum
        intro p hpL
        obtain ⟨hpI, hp⟩ := mem_filter.mp hpL
        letI : Fact p.Prime := ⟨hp⟩
        exact card_primePair_le F N p (hF p hp (mem_Ioo.mp hpI).1)
      · apply sum_le_sum
        intro p hpS
        exact card_powerPair_le N p E (mem_filter.mp hpS).2
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ ((card_filter_le _ _).trans_eq (card_range _))) _

/-- Every prime larger than a nonzero coefficient survives reduction. -/
theorem reduction_ne_zero_of_coefficient_bound (F : Polynomial ℤ) (i p : ℕ)
    (hi : F.coeff i ≠ 0) (hp : (F.coeff i).natAbs < p) :
    reduction F p ≠ 0 := by
  intro heq
  have hc : ((F.coeff i : ℤ) : ZMod p) = 0 := by
    simpa only [reduction, Polynomial.coeff_map,
      Polynomial.coeff_zero] using congrArg (fun P : Polynomial (ZMod p) => P.coeff i) heq
  have hdiv : p ∣ (F.coeff i).natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (F.coeff i) p).mp hc)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (Int.natAbs_pos.mpr hi) hdiv)

/-- A prime that can divide a positive height is at most the side length;
    this absorbs the usual endpoint error in the residue count. -/
theorem prime_pair_term_le_real (d N p : ℕ) (hp : 0 < p) (hpN : p ≤ N) :
    ((d * (N / p + 1) * (N / p) : ℕ) : ℝ) ≤
      2 * d * (N : ℝ)^2 * ((p : ℝ)^2)⁻¹ := by
  have hq : 1 ≤ N / p := Nat.div_pos hpN hp
  have hn : d * (N / p + 1) * (N / p) ≤ 2 * d * (N / p)^2 := by
    calc
      _ ≤ d * (2 * (N / p)) * (N / p) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  have hreal : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
  calc
    ((d * (N / p + 1) * (N / p) : ℕ) : ℝ) ≤
        2 * d * (((N / p : ℕ) : ℝ))^2 := by exact_mod_cast hn
    _ ≤ 2 * d * ((N : ℝ) / p)^2 := by gcongr
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- The large-prime part of the finite union has a uniform square-normalized
    bound; no prime number theorem or harmonic estimate is needed. -/
theorem large_prime_sum_le (d N K : ℕ) :
    ((∑ p ∈ (Ioo K (N + 1)).filter Nat.Prime,
      d * (N / p + 1) * (N / p) : ℕ) : ℝ) ≤
        (N : ℝ)^2 * (4 * d / (K + 1)) := by
  classical
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ p ∈ (Ioo K (N + 1)).filter Nat.Prime,
        2 * d * (N : ℝ)^2 * ((p : ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      exact prime_pair_term_le_real d N p hpP.pos (Nat.le_of_lt_succ (mem_Ioo.mp hpI).2)
    _ ≤ ∑ p ∈ Ioo K (N + 1),
        2 * d * (N : ℝ)^2 * ((p : ℝ)^2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp hnot
      positivity
    _ = 2 * d * (N : ℝ)^2 * ∑ p ∈ Ioo K (N + 1), ((p : ℝ)^2)⁻¹ := by
      rw [mul_sum]
    _ ≤ 2 * d * (N : ℝ)^2 * (2 / (K + 1)) := by
      apply mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le K (N + 1))
      positivity
    _ = _ := by ring

/-- A very coarse exponential bound already suffices for the finitely many
    small primes. -/
theorem small_prime_term_le (N K E : ℕ) :
    (((K + 1) * (N * (N / 2 ^ E)) : ℕ) : ℝ) ≤
      (N : ℝ)^2 * ((K + 1) / (E + 1)) := by
  have hpow : E + 1 ≤ 2 ^ E := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hdiv : N / 2 ^ E ≤ N / (E + 1) := Nat.div_le_div_left hpow (by omega)
  have hreal : ((N / 2 ^ E : ℕ) : ℝ) ≤ (N : ℝ) / (E + 1) := by
    calc
      _ ≤ ((N / (E + 1) : ℕ) : ℝ) := by exact_mod_cast hdiv
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_div_le (m := N) (n := E + 1) (α := ℝ))
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    ((K : ℝ) + 1) * (N * ((N / 2 ^ E : ℕ) : ℝ)) ≤
        (K + 1) * (N * ((N : ℝ) / (E + 1))) := by gcongr
    _ = _ := by ring

/-- Quantitative uniform tightness in zero-based coordinates. -/
theorem card_rangeBadPoints_le_uniform (F : Polynomial ℤ) (N K E : ℕ)
    (hF : ∀ p : ℕ, p.Prime → K < p → reduction F p ≠ 0) :
    ((rangeBadPoints F (K.factorial ^ E) N).card : ℝ) ≤
      (N : ℝ)^2 * (4 * F.natDegree / (K + 1) + (K + 1) / (E + 1)) := by
  have hn := card_rangeBadPoints_le_sum F N K E hF
  have hr : ((rangeBadPoints F (K.factorial ^ E) N).card : ℝ) ≤
      ((∑ p ∈ (Ioo K (N + 1)).filter Nat.Prime,
        F.natDegree * (N / p + 1) * (N / p) : ℕ) : ℝ) +
      (((K + 1) * (N * (N / 2 ^ E)) : ℕ) : ℝ) := by exact_mod_cast hn
  have hl := large_prime_sum_le F.natDegree N K
  have hs := small_prime_term_le N K E
  nlinarith

/-- Translating both coordinates by one identifies the counting convention
    above with the original positive square. -/
theorem badGcdCount_eq_rangeBadPoints (F : Polynomial ℤ) (M N : ℕ) :
    badGcdCount F M N = (rangeBadPoints F M N).card := by
  classical
  unfold badGcdCount
  symm
  apply card_bij (fun z _ => (z.1 + 1, z.2 + 1))
  · intro z hz
    obtain ⟨hzN, hzM⟩ := mem_filter.mp hz
    obtain ⟨ha, hh⟩ := mem_product.mp hzN
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ?_, mem_Icc.mpr ?_⟩, hzM⟩
    · exact ⟨Nat.succ_pos _, Nat.succ_le_of_lt (mem_range.mp ha)⟩
    · exact ⟨Nat.succ_pos _, Nat.succ_le_of_lt (mem_range.mp hh)⟩
  · intro z hz w hw heq
    have ha := congrArg Prod.fst heq
    have hh := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  · intro z hz
    obtain ⟨hzN, hzM⟩ := mem_filter.mp hz
    obtain ⟨ha, hh⟩ := mem_product.mp hzN
    obtain ⟨hap, haN⟩ := mem_Icc.mp ha
    obtain ⟨hhp, hhN⟩ := mem_Icc.mp hh
    have hza : z.1 - 1 + 1 = z.1 := Nat.sub_add_cancel hap
    have hzh : z.2 - 1 + 1 = z.2 := Nat.sub_add_cancel hhp
    refine ⟨(z.1 - 1, z.2 - 1), ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, ?_⟩
      · omega
      · omega
      · simpa only [value, Prod.fst, Prod.snd, hza, hzh] using hzM
    · exact Prod.ext hza hzh

/-- Uniform gcd tightness, with an explicit bound in the original square. -/
theorem badGcdCount_density_le (F : Polynomial ℤ) (N K E : ℕ) (hN : 0 < N)
    (hF : ∀ p : ℕ, p.Prime → K < p → reduction F p ≠ 0) :
    (badGcdCount F (K.factorial ^ E) N : ℝ) / (N : ℝ)^2 ≤
      4 * F.natDegree / (K + 1) + (K + 1) / (E + 1) := by
  rw [badGcdCount_eq_rangeBadPoints]
  have hNpos : (0 : ℝ) < (N : ℝ)^2 := by positivity
  apply (div_le_iff₀ hNpos).mpr
  simpa only [mul_comm] using card_rangeBadPoints_le_uniform F N K E hF

/-- The gcd of a polynomial value and an independently varying positive height
    is tight for every nonzero integer polynomial. -/
theorem gcdTight_of_ne_zero (F : Polynomial ℤ) (hF : F ≠ 0) : GcdTight F := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (8 * (F.natDegree : ℝ) / ε)
  let K := max K₀ F.leadingCoeff.natAbs
  have hK₀K : K₀ ≤ K := Nat.le_max_left _ _
  have hcoK : F.leadingCoeff.natAbs ≤ K := Nat.le_max_right _ _
  have hK : 8 * (F.natDegree : ℝ) / ε < (K : ℝ) + 1 := by
    have hcast : (K₀ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK₀K
    linarith
  have hfirst : 4 * (F.natDegree : ℝ) / ((K : ℝ) + 1) < ε / 2 := by
    have hpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    apply (div_lt_iff₀ hpos).mpr
    have hm := (div_lt_iff₀ hε).mp hK
    nlinarith
  obtain ⟨E, hE⟩ := exists_nat_gt (2 * ((K : ℝ) + 1) / ε)
  have hsecond : ((K : ℝ) + 1) / ((E : ℝ) + 1) < ε / 2 := by
    have hpos : (0 : ℝ) < (E : ℝ) + 1 := by positivity
    apply (div_lt_iff₀ hpos).mpr
    have hm := (div_lt_iff₀ hε).mp hE
    nlinarith
  refine ⟨K.factorial ^ E, Filter.eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro N hN
  apply lt_of_le_of_lt (badGcdCount_density_le F N K E hN ?_)
  · linarith
  · intro p hp hpK
    apply reduction_ne_zero_of_coefficient_bound F F.natDegree p
    · simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hF
    · simpa only [Polynomial.coeff_natDegree] using lt_of_le_of_lt hcoK hpK

end PolynomialVisibility
