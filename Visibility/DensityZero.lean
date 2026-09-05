import Visibility.Sparse

/-! Elementary closure and interval invariance of natural density zero. -/

namespace PolynomialVisibility

open Filter Finset

attribute [local instance] Classical.propDecidable

/-- A subset of a density-zero set has density zero. -/
theorem NaturalDensityZero.mono {S T : Set ℕ} (hT : NaturalDensityZero T)
    (hsub : S ⊆ T) : NaturalDensityZero S := by
  classical
  apply squeeze_zero (fun N => by positivity) _ hT
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  exact mem_filter.mpr ⟨(mem_filter.mp hn).1, hsub (mem_filter.mp hn).2⟩

/-- The empty set has density zero. -/
theorem naturalDensityZero_empty : NaturalDensityZero (∅ : Set ℕ) := by
  simp only [NaturalDensityZero, Set.mem_empty_iff_false, filter_false, card_empty,
    Nat.cast_zero, zero_div]
  exact tendsto_const_nhds

/-- The union of two density-zero sets has density zero. -/
theorem NaturalDensityZero.union {S T : Set ℕ} (hS : NaturalDensityZero S)
    (hT : NaturalDensityZero T) : NaturalDensityZero (S ∪ T) := by
  classical
  have hlimit := hS.add hT
  simp only [add_zero] at hlimit
  apply squeeze_zero (fun N => by positivity) _ hlimit
  intro N
  have hc : ((range N).filter (fun n => n ∈ S ∪ T)).card ≤
      ((range N).filter (fun n => n ∈ S)).card +
      ((range N).filter (fun n => n ∈ T)).card := by
    have heq : (range N).filter (fun n => n ∈ S ∪ T) =
        ((range N).filter (fun n => n ∈ S)) ∪ ((range N).filter (fun n => n ∈ T)) := by
      ext n
      simp only [mem_filter, Set.mem_union, mem_union]
      tauto
    rw [heq]
    exact card_union_le _ _
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hr : (((range N).filter (fun n => n ∈ S ∪ T)).card : ℝ) ≤
      (((range N).filter (fun n => n ∈ S)).card : ℝ) +
      (((range N).filter (fun n => n ∈ T)).card : ℝ) := by
    simpa only [Nat.cast_add] using (Nat.cast_le (α := ℝ)).mpr hc
  convert hr using 1
  congr 2
  ext n
  simp

/-- A union indexed by a finite set preserves density zero. -/
theorem naturalDensityZero_finset_biUnion {ι : Type*} (s : Finset ι) (S : ι → Set ℕ)
    (hS : ∀ i ∈ s, NaturalDensityZero (S i)) :
    NaturalDensityZero (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using naturalDensityZero_empty
  | @insert i s hi ih =>
    have heq : (⋃ j ∈ insert i s, S j) = S i ∪ (⋃ j ∈ s, S j) := by
      ext n
      simp only [Set.mem_iUnion, mem_insert, Set.mem_union]
      aesop
    rw [heq]
    exact (hS i (mem_insert_self _ _)).union (ih (fun j hj => hS j (mem_insert_of_mem hj)))

/-- Moving from `[0,N)` to `[1,N]` changes a count by at most one. -/
theorem card_Icc_filter_le_range_add_one (S : Set ℕ) (N : ℕ) :
    ((Icc 1 N).filter (fun n => n ∈ S)).card ≤
      ((range N).filter (fun n => n ∈ S)).card + 1 := by
  classical
  have hsub : (Icc 1 N).filter (fun n => n ∈ S) ⊆
      ((range N).filter (fun n => n ∈ S)) ∪ {N} := by
    intro n hn
    obtain ⟨hnI, hnS⟩ := mem_filter.mp hn
    have hnN := (mem_Icc.mp hnI).2
    by_cases hnlt : n < N
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr hnlt, hnS⟩)
    · exact mem_union_right _ (mem_singleton.mpr (by omega))
  simpa only [card_singleton] using (card_le_card hsub).trans (card_union_le _ _)

/-- A density-zero set also has vanishing normalized count in positive
    intervals, the convention used in the visibility problem. -/
theorem NaturalDensityZero.tendsto_Icc {S : Set ℕ} (hS : NaturalDensityZero S) :
    Tendsto (fun N : ℕ => (((Icc 1 N).filter (fun n => n ∈ S)).card : ℝ) / N)
      atTop (nhds 0) := by
  classical
  have hlimit := hS.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [add_zero] at hlimit
  apply squeeze_zero (fun N => by positivity) _ hlimit
  intro N
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast card_Icc_filter_le_range_add_one S N

/-- Membership in any fixed finite family of sparse sets remains sparse under
    the positive-interval counting convention. -/
theorem tendsto_Icc_finset_biUnion {ι : Type*} (s : Finset ι) (S : ι → Set ℕ)
    (hS : ∀ i ∈ s, NaturalDensityZero (S i)) :
    Tendsto (fun N : ℕ =>
      (((Icc 1 N).filter (fun n => n ∈ ⋃ i ∈ s, S i)).card : ℝ) / N)
      atTop (nhds 0) :=
  (naturalDensityZero_finset_biUnion s S hS).tendsto_Icc

end PolynomialVisibility
