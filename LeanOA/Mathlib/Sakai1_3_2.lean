import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions NNReal

theorem ExtremallyDisconnected_of_notSureWhatYet
    : (∀ s : Set C(K, ℝ≥0), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s →
    ∃ (f : C(K, ℝ≥0)), IsLUB s f) → ExtremallyDisconnected K :=
  by
  intro H1
  constructor
  intro U hU
  by_contra H2
  have hne : Nonempty U := by
    by_contra
    push_neg at this
    simp only [Set.isEmpty_coe_sort] at this
    rw [this, closure_empty] at H2
    simp only [isOpen_empty, not_true_eq_false] at H2
  obtain ⟨t, ht⟩ := hne
  have hR : DirectedOn (· ≤ ·) {f : C(K, ℝ≥0) | ∀ x, 0 ≤ f x ∧ f x ≤ 1} := by sorry
  have hT := H1 {f : C(K, ℝ≥0) | ∀ x, 0 ≤ f x ∧ f x ≤ 1} hR
  sorry
