import Mathlib.Analysis.InnerProductSpace.Basic
import LeanOA.Mathlib.Analysis.Normed.Extreme

open Set Metric
open scoped ComplexOrder

-- TODO: add that in a Hilbert space, `x ∈ extremePoints 𝕜 (closedBall 0 1)` iff `‖x‖ = 1`,
-- in other words, `extremePoints 𝕜 (closedBall 0 1) = sphere 0 1`
theorem InnerProductSpace.extremePoints_closedUnitBall_eq_sphere {𝕜 E}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Nontrivial E] : extremePoints 𝕜 (closedBall (0 : E) 1) = sphere 0 1 := by
  apply subset_antisymm extremePoints_closedUnitBall_subset_sphere
  simp only [Set.subset_def, mem_extremePoints, mem_sphere, dist_zero_right, mem_closedBall]
  refine fun x hx ↦ ⟨hx.le, fun y hy z hz ⟨a, b, ha, hb, hab, hxyz⟩ ↦ ?_⟩
  sorry
