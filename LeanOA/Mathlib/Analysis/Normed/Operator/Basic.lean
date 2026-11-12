module

public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

open NNReal

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E E' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- If `f` has dense range and is `K`-antilipschitz, then the norm of a continuous linear map
from the codomain of `f` is bounded by `K` multiplied by the norm of the precomposition with `f`.
See `opNorm_le_mul_opNorm_comp_of_antilipschitz_liftQL` for a version which instead assumes the
induced map `E ⧸ f.ker →SL[σ] F` is antilipschitz, rather than `f` itself. -/
theorem opNorm_le_mul_opNorm_comp_of_antilipschitz (g : E' →SL[σ] F) {f : E →L[𝕜] E'}
    (hf : DenseRange f) {K : ℝ≥0} (hK : AntilipschitzWith K f) : ‖g‖ ≤ K * ‖g.comp f‖ := by
  refine g.opNorm_le_bound (by positivity) fun y ↦ ?_
  refine hf.induction_on y (isClosed_le (by fun_prop) (by fun_prop)) fun x ↦ ?_
  calc ‖g (f x)‖ ≤ ‖g.comp f‖ * ‖x‖ := (g.comp f).le_opNorm x
    _ ≤ ‖g.comp f‖ * (K * ‖f x‖) := by gcongr; exact f.bound_of_antilipschitz hK x
    _ = K * ‖g.comp f‖ * ‖f x‖ := by ring

end ContinuousLinearMap
