module

public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

open Bornology Filter

namespace Topology.IsInducing

variable {𝕜 E ι : Type*} {Eι : ι → Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    [∀ i, AddCommGroup (Eι i)] [∀ i, Module 𝕜 (Eι i)]
    [∀ i, TopologicalSpace (Eι i)]
    {f : (i : ι) → E →ₗ[𝕜] Eι i}

/-- If the topology on `E` is induced by a family of linear maps, then a set `s : Set E` is von
Neumann bounded if and only if its image under each map is von Neumann bounded. -/
lemma isVonNBounded_iff [TopologicalSpace E]
    (hf : Topology.IsInducing (fun x i ↦ f i x))
    (s : Set E) :
    IsVonNBounded 𝕜 s ↔ ∀ i, IsVonNBounded 𝕜 (f i '' s) := by
  replace hf : IsInducing (LinearMap.pi f) := hf
  calc
    IsVonNBounded 𝕜 s ↔ IsVonNBounded 𝕜 (LinearMap.pi f '' s) := by
      simp [isVonNBounded_iff_tendsto_smallSets_nhds, hf.nhds_eq_comap,
        smallSets_comap_eq_comap_image, Function.comp_def]
    _ ↔ ∀ i, IsVonNBounded 𝕜 (f i '' s) := by simp [isVonNBounded_pi_iff, Set.image_image]

/-- If the topology on `E` is induced by a family of linear maps, then a set `s : Set E` is von
Neumann bounded if its image under each map is von Neumann bounded. -/
alias ⟨_, isVonNBounded⟩ := isVonNBounded_iff

end Topology.IsInducing
