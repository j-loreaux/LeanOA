import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UrysohnsLemma

open Set Function

variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [R1Space K]

theorem ExtremallyDisconnected.ofConditionallyCompletePartialOrderSupContinuousMap
    (h : ∀ s : Set C(K, ℝ), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → ∃ g, IsLUB s g) :
    ExtremallyDisconnected K where
  open_closure u hu := by
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
    have hf0 x : 0 ≤ f x := hf.1 hs_zero x
    have h0 : EqOn f 0 (closure u)ᶜ := by
      intro x hx
      obtain ⟨g, hg0, hg_eqOn, hg⟩ := exists_continuous_zero_one_of_isCompact
        (isCompact_singleton (x := x)) (t := closure u) isClosed_closure (by aesop)
      apply le_antisymm
      · trans f x * g x
        · refine @hf.2 (f * g) (fun j hj y ↦ ?_) x
          by_cases hy : j y = 0
          · simpa [hy] using mul_nonneg (hf0 y) (hg y).1
          · replace hy := subset_closure <| hj.1 <| mem_support.mpr hy
            aesop
        · simp_all
      · exact hf.1 hs_zero x
    have key : (closure u)ᶜ = f ⁻¹' {0} := by
      ext x
      refine ⟨@h0 x, fun hx ↦ ?_⟩
      contrapose! hx
      simp [h1 (by simpa using hx)]
    simpa [← isClosed_compl_iff, key] using isClosed_singleton.preimage (map_continuous f)

open scoped ComplexOrder

open ContinuousMap RCLike in
/-- If `C(K, 𝕜)` is a conditionally complete partial order for `RCLike 𝕜`, then
`K` is extremally disconnected. -/
theorem ExtremallyDisconnected.ofConditionallyCompletePartialOrderSupContinuousMapRCLike
    {𝕜 : Type*} [RCLike 𝕜]
    (h : ∀ s : Set C(K, 𝕜), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → ∃ g, IsLUB s g) :
    ExtremallyDisconnected K := by
  refine .ofConditionallyCompletePartialOrderSupContinuousMap (fun s hs hsn hb ↦ ?_)
  let coe : C(ℝ, 𝕜) := ⟨ofReal, continuous_ofReal⟩
  let coeComp : C(K, ℝ) → C(K, 𝕜) := coe.comp
  have coe_mono : Monotone coeComp := fun f g hfg x ↦ by simpa [coeComp, coe] using hfg x
  obtain ⟨g', hg⟩ := h _ (hs.mono_comp coe_mono) (hsn.image _) (coe_mono.map_bddAbove hb)
  let reCM : C(𝕜, ℝ) := ⟨re, continuous_re⟩
  obtain ⟨g, rfl⟩ : ∃ g, coeComp g = g' := by
    use reCM.comp g'
    ext x
    obtain ⟨-, h_im⟩ : _ ∧ 0 = im (g' x) := by
      simpa [le_iff_re_im (K := 𝕜), coeComp, coe] using hg.1 ⟨_, hsn.some_mem, rfl⟩ x
    simpa [coeComp, coe, reCM, ← conj_eq_iff_re, conj_eq_iff_im] using h_im.symm
  exact ⟨g, hg.of_image <| by simp [ContinuousMap.le_def, coeComp, coe]⟩
