import Mathlib.Analysis.InnerProductSpace.Basic
import LeanOA.Mathlib.Analysis.Normed.Extreme

open Set Metric
open scoped ComplexOrder

-- TODO: add that in a Hilbert space, `x ∈ extremePoints 𝕜 (closedBall 0 1)` iff `‖x‖ = 1`,
-- in other words, `extremePoints 𝕜 (closedBall 0 1) = sphere 0 1`
proof_wanted InnerProductSpace.extremePoints_closedUnitBall_eq_sphere {𝕜 E}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Nontrivial E] : extremePoints 𝕜 (closedBall (0 : E) 1) = sphere 0 1
