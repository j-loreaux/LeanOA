import Mathlib.Analysis.LocallyConvex.Polar
import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin

open WeakBilin
theorem LinearMap.isClosed_polar {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    IsClosed ((pairing B.flip).flip.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (eval_continuous (pairing B.flip) _)
