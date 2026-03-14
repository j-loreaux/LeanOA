import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions NNReal

/- Temporarily removed ℝ≥0 everywhere in order to access Urysohn from Mathlib. -/
theorem ExtremallyDisconnected_of_notSureWhatYet
    : (∀ s : Set C(K, ℝ), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s →
    ∃ (g : C(K, ℝ)), IsLUB s g) → ExtremallyDisconnected K :=
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
  have hR : DirectedOn (· ≤ ·) {f : C(K, ℝ) | ∀ x, 0 ≤ f x ∧ f x ≤ 1} := by sorry
  obtain ⟨w, hw0, hw1, hwIcc⟩ := exists_continuous_zero_one_of_isClosed
      (X := K) (t := {t}) (s := Uᶜ) (by aesop) (by aesop) (by aesop)
  have hNE : {f : C(K, ℝ) | ∀ (x : K), 0 ≤ f x ∧ f x ≤ 1}.Nonempty := by
    use w
    exact Set.mem_setOf.mpr hwIcc
  have hBA : BddAbove {f : C(K, ℝ) | ∀ (x : K), 0 ≤ f x ∧ f x ≤ 1} :=
    ⟨1, fun f Hf x ↦ (Hf x).2⟩
  have hT := H1 {f : C(K, ℝ) | ∀ x, 0 ≤ f x ∧ f x ≤ 1} hR hNE hBA
  sorry
