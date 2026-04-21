import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin

variable {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The weak dual of `E` is continuously linearly equivalent to the `WeakBilin` induced by the
`topDualPairing 𝕜 E`. This is essentially a definitional equivalence, but to avoid abuse of
definitional equality it is implemented without `ContinuousLinearEquiv.refl`. -/
def WeakDual.weakBilinCLE : WeakDual 𝕜 E ≃L[𝕜] WeakBilin (topDualPairing 𝕜 E) where
  toLinearEquiv := WeakDual.toStrongDual ≪≫ₗ (WeakBilin.linearEquiv 𝕜 (topDualPairing 𝕜 E)).symm
  continuous_toFun := WeakBilin.continuous_of_continuous_eval' _ WeakDual.eval_continuous
  continuous_invFun :=WeakDual.continuous_of_continuous_eval <| WeakBilin.eval_continuous' _

/-- The topological vector space `E` equipped with the weak topology is continuously linearly
equivalent to the `WeakBilin` induced by the `(topDualPairing 𝕜 E).flip`. This is essentially a
definitional equivalence, but to avoid abuse of definitional equality it is implemented without
`ContinuousLinearEquiv.refl`. -/
def WeakSpace.weakBilinCLE : WeakSpace 𝕜 E ≃L[𝕜] WeakBilin (topDualPairing 𝕜 E).flip where
  toLinearEquiv := (toWeakSpace 𝕜 E).symm ≪≫ₗ
    (WeakBilin.linearEquiv 𝕜 (topDualPairing 𝕜 E).flip).symm
  continuous_toFun := WeakBilin.continuous_of_continuous_eval' _ <| WeakBilin.eval_continuous _
  continuous_invFun := WeakBilin.continuous_of_continuous_eval _ <| WeakBilin.eval_continuous' _

section Banach_Alaoglu

variable (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜]

open Set Topology WeakDual Metric

-- is this the right generality?
theorem Bornology.isVonNBounded_image (s : Set E) {f : E → 𝕜} {r : ℝ}
    (hf : ∀ u ∈ s, ‖f u‖ ≤ r) : Bornology.IsVonNBounded 𝕜 (f '' s) := by
  aesop (add simp NormedSpace.isVonNBounded_iff')

variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

-- what's the right generality for this?
variable (E) in
theorem WeakDual.isInducing_dFunLikeCoe :
    IsInducing (DFunLike.coe : WeakDual 𝕜 E → (E → 𝕜)) where eq_induced := rfl

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

-- deprime and replace the original
lemma WeakDual.isClosed_image_polar_of_mem_nhds' {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsClosed (DFunLike.coe '' polar 𝕜 s) :=
  have : DFunLike.coe '' polar 𝕜 s = {f : E → 𝕜 | ∀ (x y : E), f (x + y) = f x + f y} ∩
      {f : E → 𝕜 | ∀ (c : 𝕜) (x : E), f (c • x) = c • f x} ∩
        ⋂ u ∈ s, (fun f : E → 𝕜 => ‖f u‖) ⁻¹' Set.Iic 1 := by
    refine subset_antisymm_iff.mpr ⟨fun _ hf ↦ ?_, fun f ↦ ?_⟩
    · rcases hf with ⟨φ, hφ, rfl⟩; simpa
    simpa using fun hf1 hf2 hf3 ↦ ⟨LinearMap.clmOfExistsBoundedImage
        { toFun := f, map_add' := hf1, map_smul' := hf2 }
        ⟨s, s_nhds, Bornology.isVonNBounded_image 𝕜 s hf3⟩,
      mem_preimage.mp hf3, rfl⟩
  this ▸ ((isClosed_setOf_map_add E 𝕜).inter (isClosed_setOf_map_smul E 𝕜 id)).inter
    (isClosed_biInter fun u _ ↦ isClosed_Iic.preimage (continuous_apply u).norm)

-- deprime and replace the original
theorem WeakDual.isCompact_polar' [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsCompact (polar 𝕜 s) := by
  suffices IsCompact (DFunLike.coe '' polar 𝕜 s) by
    simpa [(DFunLike.coe_injective (β := fun _ ↦ 𝕜)).preimage_image <| polar 𝕜 s] using
      (WeakDual.isInducing_dFunLikeCoe 𝕜 E).isCompact_preimage' this
  obtain ⟨r, hr⟩ : ∃ r : E → ℝ,
      DFunLike.coe '' polar 𝕜 s ⊆ univ.pi fun v ↦ Metric.closedBall 0 (r v) := by
    suffices ∀ v : E, ∃ r : ℝ, ∀ φ ∈ polar 𝕜 s, ‖φ v‖ ≤ r by
      choose r hr using this
      aesop (add simp subset_def)
    intro v
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff (s := (fun x : 𝕜 ↦ x • v) ⁻¹' s) (x := 0).mp <| by
      simpa using Continuous.continuousAt (by fun_prop) (by simpa)
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt 𝕜 hε
    refine ⟨1 / ‖c‖, fun φ hφ ↦ ?_⟩
    simpa only [le_div_iff₀ hc0, mul_comm, ← norm_smul, map_smul] using hφ _ (h (by simpa using hc))
  exact (isCompact_univ_pi <| fun i ↦ ProperSpace.isCompact_closedBall 0 (r i)).of_isClosed_subset
    (isClosed_image_polar_of_mem_nhds' 𝕜 s_nhds) hr

end Banach_Alaoglu
