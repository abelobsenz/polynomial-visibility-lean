import Mathlib

/-!
# A finite prime-power certificate for a bounded gcd

The analytic tightness argument discards two kinds of pairs: those with a
common prime larger than a cutoff, and those whose second coordinate is
divisible by a high power of a small prime. The lemmas below verify the exact
arithmetic certificate underlying that argument.
-/

namespace PolynomialVisibility

/-- A nonzero integer with bounded prime support and bounded prime exponents
    divides an explicit constant depending only on the two cutoffs. -/
theorem dvd_factorial_pow_of_prime_cutoffs
    {g K E : ℕ} (hg : g ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ g → p ≤ K)
    (hexponent : ∀ p : ℕ, p.Prime → p ≤ K → ¬ p ^ E ∣ g) :
    g ∣ K.factorial ^ E := by
  apply (Nat.factorization_le_iff_dvd hg
    (pow_ne_zero _ (Nat.factorial_ne_zero K))).mp
  intro p
  by_cases hz : g.factorization p = 0
  · simp [hz]
  have hdata : p.Prime ∧ p ∣ g ∧ g ≠ 0 := by
    simpa only [Nat.factorization_eq_zero_iff, not_or, not_not] using hz
  obtain ⟨hp, hpg, _⟩ := hdata
  have hpK := hsupport p hp hpg
  have he : g.factorization p < E := by
    have := hexponent p hp hpK
    rwa [hp.pow_dvd_iff_le_factorization hg, not_le] at this
  have hfac : 1 ≤ K.factorial.factorization p :=
    (hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero K)).mp
      (Nat.dvd_factorial hp.pos hpK)
  simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] using
    (le_trans (Nat.le_of_lt he) (Nat.le_mul_of_pos_right E hfac))

/-- If no exceptional prime event occurs, the gcd is bounded independently of
    the coordinates. This includes `v = 0`, provided the height is positive. -/
theorem gcd_le_factorial_pow_of_prime_cutoffs
    {v h K E : ℕ} (hh : 0 < h)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.gcd v h → p ≤ K)
    (hexponent : ∀ p : ℕ, p.Prime → p ≤ K → ¬ p ^ E ∣ h) :
    Nat.gcd v h ≤ K.factorial ^ E := by
  apply Nat.le_of_dvd (pow_pos (Nat.factorial_pos K) E)
  apply dvd_factorial_pow_of_prime_cutoffs (Nat.gcd_ne_zero_right hh.ne') hsupport
  intro p hp hpK hpE
  exact hexponent p hp hpK (hpE.trans (Nat.gcd_dvd_right v h))

/-- Contrapositive form: a large gcd forces either a large common prime or a
    high power of a small prime dividing the height. -/
theorem large_gcd_has_prime_exception
    {v h K E : ℕ} (hh : 0 < h)
    (hlarge : K.factorial ^ E < Nat.gcd v h) :
    (∃ p : ℕ, p.Prime ∧ K < p ∧ p ∣ v ∧ p ∣ h) ∨
    (∃ p : ℕ, p.Prime ∧ p ≤ K ∧ p ^ E ∣ h) := by
  by_contra hnot
  push_neg at hnot
  have hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.gcd v h → p ≤ K := by
    intro p hp hpg
    by_contra hpK
    exact hnot.1 p hp (lt_of_not_ge hpK)
      (hpg.trans (Nat.gcd_dvd_left v h)) (hpg.trans (Nat.gcd_dvd_right v h))
  have hexponent : ∀ p : ℕ, p.Prime → p ≤ K → ¬ p ^ E ∣ h := by
    intro p hp hpK
    exact hnot.2 p hp hpK
  exact (not_lt_of_ge (gcd_le_factorial_pow_of_prime_cutoffs hh hsupport hexponent)) hlarge

/-- A set of residue classes has at most one preimage for each quotient and
    residue, giving the elementary interval bound. Positive coordinates are
    represented here by `a + 1` for `a ∈ range N`. -/
theorem card_residue_preimage_le (N p : ℕ) (R : Finset (ZMod p)) :
    ((Finset.range N).filter (fun a => ((a + 1 : ℕ) : ZMod p) ∈ R)).card ≤
      (N / p + 1) * R.card := by
  classical
  let s := (Finset.range N).filter (fun a => ((a + 1 : ℕ) : ZMod p) ∈ R)
  let t := (Finset.range (N / p + 1)) ×ˢ R
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (fun a => ((a + 1) / p, ((a + 1 : ℕ) : ZMod p)))
    · intro a ha
      change a ∈ (Finset.range N).filter (fun a => ((a + 1 : ℕ) : ZMod p) ∈ R) at ha
      obtain ⟨haN, haR⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr ?_, haR⟩
      have ha : a + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp haN)
      exact Nat.lt_succ_of_le (Nat.div_le_div_right ha)
    · intro a ha b hb hab
      have hdiv : (a + 1) / p = (b + 1) / p := congrArg Prod.fst hab
      have hcast : ((a + 1 : ℕ) : ZMod p) = ((b + 1 : ℕ) : ZMod p) :=
        congrArg Prod.snd hab
      have hmod := (ZMod.natCast_eq_natCast_iff' (a + 1) (b + 1) p).mp hcast
      have ha := Nat.mod_add_div (a + 1) p
      have hb := Nat.mod_add_div (b + 1) p
      rw [hdiv, hmod] at ha
      omega
  simpa only [t, Finset.card_product, Finset.card_range] using hcard

/-- Reduction of an integer polynomial modulo a prime. -/
noncomputable def reduction (F : Polynomial ℤ) (p : ℕ) : Polynomial (ZMod p) :=
  F.map (Int.castRingHom (ZMod p))

/-- Polynomial evaluation commutes with reduction, expressed as divisibility
    of the absolute value of the original integer value. -/
theorem reduction_eval_eq_zero_iff (F : Polynomial ℤ) (p a : ℕ) :
    (reduction F p).eval (a : ZMod p) = 0 ↔
      p ∣ (F.eval (a : ℤ)).natAbs := by
  unfold reduction
  rw [Polynomial.eval_map]
  have hcast : (a : ZMod p) = (Int.castRingHom (ZMod p)) (a : ℤ) := by simp
  rw [hcast, Polynomial.eval₂_at_apply]
  change ((F.eval (a : ℤ) : ℤ) : ZMod p) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]

/-- A nonzero reduction modulo a prime has at most `natDegree F` roots. -/
theorem card_reduction_roots_le (F : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (hF : reduction F p ≠ 0) :
    (Finset.univ.filter (fun x : ZMod p => (reduction F p).eval x = 0)).card ≤
      F.natDegree := by
  apply le_trans (Polynomial.card_le_degree_of_subset_roots (p := reduction F p) ?_)
    Polynomial.natDegree_map_le
  intro x hx
  apply (Polynomial.mem_roots hF).mpr
  exact (Finset.mem_filter.mp hx).2

/-- Prime divisibility of polynomial values in an interval has the expected
    elementary upper bound, without any equidistribution input. -/
theorem card_prime_divides_values_le (F : Polynomial ℤ) (N p : ℕ) [Fact p.Prime]
    (hF : reduction F p ≠ 0) :
    ((Finset.range N).filter (fun a => p ∣ (F.eval ((a + 1 : ℕ) : ℤ)).natAbs)).card ≤
      (N / p + 1) * F.natDegree := by
  classical
  let R := Finset.univ.filter (fun x : ZMod p => (reduction F p).eval x = 0)
  have heq :
      ((Finset.range N).filter (fun a => p ∣ (F.eval ((a + 1 : ℕ) : ℤ)).natAbs)) =
      ((Finset.range N).filter (fun a => ((a + 1 : ℕ) : ZMod p) ∈ R)) := by
    ext a
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and,
      reduction_eval_eq_zero_iff]
  rw [heq]
  exact (card_residue_preimage_le N p R).trans
    (Nat.mul_le_mul_left _ (card_reduction_roots_le F p hF))

end PolynomialVisibility
