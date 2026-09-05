import Visibility.Definitions

namespace PolynomialVisibility

/-- A finite set preserved by an affine strict contraction has at most one point. -/
theorem finite_affine_contraction_subsingleton
    (S : Finset ℂ) (α : ℝ) (β : ℂ) (hα0 : 0 < α) (hα1 : α < 1)
    (hmap : ∀ z ∈ S, (α : ℂ) * z + β ∈ S) :
    ∀ z ∈ S, ∀ w ∈ S, z = w := by
  classical
  intro z hz w hw
  have hinj : Function.Injective (fun z : ℂ => (α : ℂ) * z + β) := by
    intro x y h
    have hα : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα0
    exact mul_left_cancel₀ hα (add_right_cancel h)
  have hsurj : Set.SurjOn (fun z : ℂ => (α : ℂ) * z + β) (↑S) (↑S) :=
    Finset.surjOn_of_injOn_of_card_le _ hmap hinj.injOn (le_refl _)
  obtain ⟨p, hp, hmax⟩ := (S ×ˢ S).exists_max_image
    (fun p : ℂ × ℂ => ‖p.1 - p.2‖) ⟨(z, w), by simp [hz, hw]⟩
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨x, hx, hxp⟩ := hsurj hp1
  obtain ⟨y, hy, hyp⟩ := hsurj hp2
  have hbound : ‖x - y‖ ≤ ‖p.1 - p.2‖ := hmax (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)
  have heq : ‖p.1 - p.2‖ = α * ‖x - y‖ := by
    rw [← hxp, ← hyp]
    have h : (α : ℂ) * x + β - ((α : ℂ) * y + β) = (α : ℂ) * (x - y) := by ring
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα0]
  have hzero : ‖p.1 - p.2‖ = 0 := by
    have hnonneg := norm_nonneg (p.1 - p.2)
    have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt hα0)
    nlinarith
  have hzw := hmax (z, w) (by simp [hz, hw])
  rw [hzero] at hzw
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzw (norm_nonneg _)))

/-- A nonzero polynomial with distinct roots admits no proper positive affine scaling. -/
theorem no_affine_contraction_identity (P : Polynomial ℂ) (hP : P ≠ 0)
    (z w : ℂ) (hzw : z ≠ w) (hz : P.IsRoot z) (hw : P.IsRoot w)
    (α : ℝ) (β q : ℂ) (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ (∀ x : ℂ, P.eval ((α : ℂ) * x + β) = q * P.eval x) := by
  classical
  intro hid
  let S := P.roots.toFinset
  have hmem : ∀ x, x ∈ S ↔ P.IsRoot x := by
    intro x
    simp [S, Polynomial.mem_roots hP]
  have hmap : ∀ x ∈ S, (α : ℂ) * x + β ∈ S := by
    intro x hx
    apply (hmem _).mpr
    change P.eval _ = 0
    rw [hid, (hmem x).mp hx]
    simp
  exact hzw (finite_affine_contraction_subsingleton S α β hα0 hα1 hmap
    z ((hmem z).mpr hz) w ((hmem w).mpr hw))

end PolynomialVisibility
