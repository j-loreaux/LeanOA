import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions NNReal

-- This can work inline.
example {A : Set K} : IsClosed A ↔ closure A ∩ Aᶜ = ∅ :=
  ⟨fun _ ↦ by simp, fun H ↦ closure_subset_iff_isClosed.mp <| Set.diff_eq_empty.mp H⟩

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
  have hNE : {f : C(K, ℝ) | ∀ (x : K), 0 ≤ f x ∧ f x ≤ 1}.Nonempty :=
    ⟨w, Set.mem_setOf.mpr hwIcc⟩
  have hBA : BddAbove {f : C(K, ℝ) | ∀ (x : K), 0 ≤ f x ∧ f x ≤ 1} :=
    ⟨1, fun f Hf x ↦ (Hf x).2⟩
  obtain ⟨g, hg⟩ := H1 {f : C(K, ℝ) | ∀ x, 0 ≤ f x ∧ f x ≤ 1} hR hNE hBA
  have hRLe: w t ≤ g t := (hg.1 <| Set.mem_setOf.mpr hwIcc) t
  have hle : ∀ r ∈ U, 1 ≤ g r := by
    intro r hR
    obtain ⟨w, hw0, hw1, hwIcc⟩ := exists_continuous_zero_one_of_isClosed
        (X := K) (t := {r}) (s := Uᶜ) (by aesop) (by aesop) (by aesop)
    have : w r ≤ g r := (hg.1 <| Set.mem_setOf.mpr hwIcc) r
    rwa [hw1, Pi.one_apply] at this
    exact Set.mem_singleton r
  have heq: ∀ r ∈ U , 1 = g r := by
    intro r hrU
    apply le_antisymm
    · exact hle r hrU
    · have : (1 : C(K, ℝ)) ∈ upperBounds {f | ∀ (x : K), 0 ≤ f x ∧ f x ≤ 1} :=
        fun a ha ↦ fun x ↦ ((fun a ↦ (ha x).2) ∘ U) t
      exact RCLike.ofReal_le_ofReal.mp (hg.2 this r)
  have ht : Set.EqOn g (fun x => 1) U := Set.EqOn.symm heq
  have heqonclos: ∀ x ∈ closure U, Set.EqOn g (fun x => 1) (closure U) := by
    intro x hx
    apply ContinuousWithinAt.eqOn_const_closure (X := K) (Y := ℝ) (c := 1) (s := U) (f := g)
    · exact fun y hy ↦ map_continuousWithinAt g U y
    · exact ht
  have hclsub : (closure U)ᶜ ⊆ Uᶜ := Set.compl_subset_compl_of_subset <| subset_closure
  have heqonc : Set.EqOn w 0 (closure U)ᶜ :=
    Set.EqOn.symm (Set.EqOn.symm fun ⦃x⦄ a ↦ hw0 (hclsub a))
  have : ¬ IsClosed (closure U)ᶜ := by simpa [isClosed_compl_iff]
  rw [hw1, Pi.one_apply] at hRLe
  · --adapt above exercise and use this to get contra.
    sorry
  · exact Set.mem_singleton t
