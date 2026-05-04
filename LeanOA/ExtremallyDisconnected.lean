import LeanOA.Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UrysohnsLemma

open Set Function ContinuousMap RCLike
open scoped ComplexOrder

variable {K 𝕜 : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [R1Space K] [RCLike 𝕜]

/-- If `C(K, 𝕜)` is a conditionally complete partial order for `RCLike 𝕜`, then
`K` is extremally disconnected. -/
theorem ExtremallyDisconnected.ofConditionallyCompletePartialOrderSupContinuousMap
    (h : ∀ s : Set C(K, 𝕜), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → ∃ g, IsLUB s g) :
    ExtremallyDisconnected K := by
  refine { open_closure u hu := ?_ }
  suffices h : ∀ s : Set C(K, ℝ), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → ∃ g, IsLUB s g by
    let s : Set C(K, ℝ) := {f | support f ⊆ u ∧ ∀ x, f x ∈ Icc 0 1}
    have hs_one : 1 ∈ upperBounds s := fun f hf x ↦ (hf.2 x).2
    have hs_zero : 0 ∈ s := by simp [s]
    obtain ⟨f, hf⟩ :  ∃ f, IsLUB s f := by
      refine h s (fun f hf g hg ↦ ⟨f ⊔ g, ⟨?_, by simp; grind⟩, by simp⟩)
        ⟨0, hs_zero⟩ ⟨1, hs_one⟩
      grw [ContinuousMap.coe_sup, Pi.sup_def, support_max f g]
      exact Set.union_subset hf.1 hg.1
    have h1 : EqOn f 1 (closure u) := by
      refine .closure (fun x hx ↦ ?_) (by fun_prop) (by fun_prop)
      apply le_antisymm (hf.2 hs_one x)
      obtain ⟨g, hg1, -, hg_supp, hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
        (isCompact_singleton (x := x)) hu (by simpa)
      have := @hf.1 g ⟨by grw [subset_tsupport, hg_supp], hg⟩ x
      simp_all
    have h0 : EqOn f 0 (closure u)ᶜ := fun x hx ↦ by
      obtain ⟨g, hg0, hg_eqOn, hg⟩ := exists_continuous_zero_one_of_isCompact
        (isCompact_singleton (x := x)) (t := closure u) isClosed_closure (by aesop)
      refine le_antisymm ?_ (hf.1 hs_zero x)
      trans f x * g x
      · refine @hf.2 (f * g) (fun j hj y ↦ ?_) x
        by_cases hy : j y = 0
        · simpa [hy] using mul_nonneg (hf.1 hs_zero y) (hg y).1
        · replace hy := subset_closure <| hj.1 <| mem_support.mpr hy
          aesop
      · simp_all
    have key : (closure u)ᶜ = f ⁻¹' {0} := by
      ext x
      refine ⟨@h0 x, fun hx ↦ ?_⟩
      contrapose! hx
      simp [h1 (by simpa using hx)]
    simpa [← isClosed_compl_iff, key] using isClosed_singleton.preimage (map_continuous f)
  intro s hs hsn hb
  obtain ⟨g', hg⟩ := h _ (hs.mono_comp (realToRCLike_monotone K 𝕜)) (hsn.image _)
    ((realToRCLike_monotone K 𝕜).map_bddAbove hb)
  rw [← isSelfAdjoint_realToRCLike.of_ge (hg.1 ⟨_, hsn.some_mem, rfl⟩)
    |>.realToRCLike_rclikeToReal] at hg
  exact ⟨_, hg.of_image <| by simp [le_def]⟩
