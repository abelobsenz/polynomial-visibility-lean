import Mathlib

/-!
# Visibility along an integral polynomial

The definitions use positive natural coordinates, and rational scaling as in the
question. Density is measured in the squares `1 ≤ a,h ≤ N`.
-/

namespace PolynomialVisibility

/-- A rational number is a positive integer. -/
def IsPositiveInteger (q : ℚ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ q = (k : ℚ)

/-- Exact rational-scaling definition of visibility from the question. -/
def Visible (F : Polynomial ℤ) (a h : ℕ) : Prop :=
  0 < a ∧ 0 < h ∧
  ∃ t : ℚ,
    (h : ℚ) = t * ((F.eval (a : ℤ) : ℤ) : ℚ) ∧
    ∀ u : ℕ, 0 < u → IsPositiveInteger (t * ((F.eval (u : ℤ) : ℤ) : ℚ)) → a ≤ u

/-- An invisible point still has two positive coordinates. -/
def Invisible (F : Polynomial ℤ) (a h : ℕ) : Prop :=
  0 < a ∧ 0 < h ∧ ¬ Visible F a h

/-- Positive lattice points in the square of side `N`. -/
def square (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)

/-- Number of visible lattice points in a square. -/
noncomputable def visibleCount (F : Polynomial ℤ) (N : ℕ) : ℕ := by
  classical
  exact ((square N).filter fun p => Visible F p.1 p.2).card

/-- The visible points have square density one. -/
def HasVisibilityDensityOne (F : Polynomial ℤ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => (visibleCount F N : ℝ) / (N : ℝ) ^ 2)
    Filter.atTop (nhds 1)

/-- The polynomial has at least two distinct complex roots. -/
def HasTwoDistinctRoots (F : Polynomial ℤ) : Prop :=
  ∃ z w : ℂ, z ≠ w ∧ F.aeval z = 0 ∧ F.aeval w = 0

/-- The zero polynomial has no visible positive lattice points. -/
theorem zero_not_visible (a h : ℕ) : ¬ Visible 0 a h := by
  rintro ⟨_, hh, t, heq, _⟩
  simp only [Polynomial.eval_zero, Int.cast_zero, mul_zero] at heq
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)) heq

end PolynomialVisibility

namespace PolynomialVisibility

@[simp] theorem visibleCount_zero (N : ℕ) : visibleCount 0 N = 0 := by
  simp [visibleCount, zero_not_visible]

theorem zero_has_two_distinct_roots : HasTwoDistinctRoots 0 := by
  refine ⟨0, 1, zero_ne_one, ?_, ?_⟩ <;> simp

theorem zero_not_density_one : ¬ HasVisibilityDensityOne 0 := by
  simp [HasVisibilityDensityOne]

/-- The literal statement, if it permits the zero polynomial, is false. -/
theorem literal_conjecture_false :
    ¬ ∀ F : Polynomial ℤ, HasTwoDistinctRoots F → HasVisibilityDensityOne F := by
  intro h
  exact zero_not_density_one (h 0 zero_has_two_distinct_roots)

end PolynomialVisibility
