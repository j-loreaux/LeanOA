module

public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

open scoped Pointwise
open Bornology

variable {𝕜 E ι : Type*} {Eι : ι → Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    [∀ i, AddCommGroup (Eι i)] [∀ i, Module 𝕜 (Eι i)]
    [∀ i, TopologicalSpace (Eι i)]
    (f : (i : ι) → E →ₗ[𝕜] Eι i)

namespace Bornology

lemma isVonNBounded_iff_of_iInf_induced
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    @IsVonNBounded 𝕜 E _ _ _ (⨅ i, .induced (f i) inferInstance) s := by
  simp_rw [isVonNBounded_iff] at hs ⊢
  intro v hv
  rw [nhds_iInf, Filter.mem_iInf] at hv
  obtain ⟨I, hI_fin, u, hu, rfl⟩ := hv
  have := hI_fin.to_subtype
  rw [absorbs_iInter]
  simp only [nhds_induced, map_zero, Filter.mem_comap] at hu
  intro i
  obtain ⟨t, ht, htu⟩ := hu i
  specialize hs i t ht
  filter_upwards [hs, isBounded_singleton (x := 0) |>.compl] with c hc hc₀
  -- alternate proof insteead of hte `calc` block.
  -- grw [Set.subset_preimage_image (f i) s, hc, IsUnit.mk0 c hc₀ |>.preimage_smul_set .., htu]
  calc
    s ⊆ f i ⁻¹' (f i '' s) := Set.subset_preimage_image ..
    _ ⊆ f i ⁻¹' (c • t) := by gcongr
    _ = c • f i ⁻¹' t := IsUnit.mk0 c hc₀ |>.preimage_smul_set ..
    _ ⊆ c • u i := by gcongr

lemma isVonNBounded_iff_of_iInf_induced'
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    @IsVonNBounded 𝕜 E _ _ _ (.induced (fun x i ↦  f i x) Pi.topologicalSpace) s := by
  convert isVonNBounded_iff_of_iInf_induced f s hs
  exact induced_to_pi fun x i ↦ (f i) x

end Bornology

namespace Topology.IsInducing

/-- If the topology on `E` is induced by a family of linear maps, then a set `s : Set E` is von
Neumann bounded if its image under each map is von Neumann bounded. -/
lemma isVonNBounded [TopologicalSpace E]
    (hf : Topology.IsInducing (fun x i ↦ f i x))
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    IsVonNBounded 𝕜 s :=
  hf.eq_induced ▸ isVonNBounded_iff_of_iInf_induced' f s hs

/-- If the topology on `E` is induced by a family of linear maps, then a set `s : Set E` is von
Neumann bounded if and only if its image under each map is von Neumann bounded. -/
lemma isVonNBounded_iff [TopologicalSpace E]
    (hf : Topology.IsInducing (fun x i ↦ f i x))
    (s : Set E) :
    IsVonNBounded 𝕜 s ↔ ∀ i, IsVonNBounded 𝕜 (f i '' s) := by
  -- this is stupid because the `CanLift` instance for linear maps to continuous
  -- linear maps assumes finite dimensionality.
  have (i : ι) : Continuous (f i) := by
    have := hf.continuous
    rw [continuous_pi_iff] at this
    exact this i
  let F : (i : ι) → E →L[𝕜] Eι i := fun i ↦ ⟨f i, this i⟩
  have (i : ι) : ⇑(F i) = f i := by simp [F]
  simp_rw [← this]
  exact ⟨fun hs i ↦ hs.image _, hf.isVonNBounded f s⟩

end Topology.IsInducing
