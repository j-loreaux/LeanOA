module

public import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
public import LeanOA.Mathlib.Analysis.LocallyConvex.Bounded
public import LeanOA.Mathlib.Analysis.Normed.Group.Uniform

@[expose] public section

open Bornology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

namespace WeakBilin

lemma isVonNBounded_iff (s : Set (WeakBilin B)) :
    IsVonNBounded 𝕜 s ↔ ∀ y, IsVonNBounded 𝕜 (((pairing B).flip y) '' s) :=
  WeakBilin.isInducing B |>.isVonNBounded_iff (pairing B).flip s

variable {B} in
lemma isVonNBounded_iff_bddAbove {s : Set (WeakBilin B)} :
    IsVonNBounded 𝕜 s ↔ ∀ y, BddAbove ((‖(pairing B).flip y ·‖) '' s) := by
  have (y : F) : BddBelow ((‖pairing B · y‖) '' s) := ⟨0, by rintro - ⟨_, -, rfl⟩; positivity⟩
  rw [WeakBilin.isVonNBounded_iff]
  congr! with y
  rw [← Bornology.isBounded_iff_isVonNBounded, NormedSpace.vonNBornology_eq 𝕜,
    ← isBounded_norm_iff, Set.image_image, isBounded_iff_bddBelow_bddAbove]
  simp [this]

end WeakBilin
