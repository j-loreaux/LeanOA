module

public import Mathlib.Analysis.LocallyConvex.Polar
public import LeanOA.IsWeak
public import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin

@[expose] public section

open scoped Pointwise
open WeakBilin

namespace LinearMap

theorem isClosed_polar {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    [hB : B.flip.IsWeak] (s : Set E) :
    IsClosed (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (IsWeak.continuous_eval B.flip _)

theorem isClosed_polar' {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    IsClosed ((pairing B.flip).flip.polar s) :=
  isClosed_polar (pairing B.flip).flip s

variable {𝕜 E F E' F' : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup E'] [Module 𝕜 E']
    [AddCommGroup F'] [Module 𝕜 F']
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- we should generalize this to `IsScalarTower`.
lemma polar_smul (s : Set E) (c : 𝕜) (hc : c ≠ 0) : B.polar (c • s) = c⁻¹ • B.polar s := by
  ext x
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  simp [polar, Set.mem_smul_set]
  simp [← Units.smul_def, smul_eq_iff_eq_inv_smul, ← Units.val_inv_eq_inv_val]
  simp [Units.smul_def]
  -- clean up later.

lemma smul_mem_polar_iff (s : Set E) (c : 𝕜) (hc : c ≠ 0) (y : F) :
    c • y ∈ B.polar s ↔ ∀ x ∈ s, ‖B x y‖ ≤ ‖c‖⁻¹ := by
  simp only [polar_mem_iff, map_smul, smul_eq_mul, norm_mul]
  congr! 2 with x hx
  rw [← inv_inv ‖c‖, inv_mul_le_one₀ (by simpa), inv_inv]

end LinearMap
