import LeanOA.Ultraweak.Basic
import LeanOA.PositiveContinuousLinearMap
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation

instance ContinuousSMul.complexToReal {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : ContinuousSMul ℝ E :=
  IsScalarTower.continuousSMul ℂ

open scoped Ultraweak ComplexOrder

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

-- Sakai 1.7.2
lemma sakai_1_7_2 (a : σ(M, P)) (ha₁ : IsSelfAdjoint a) (ha₂ : ¬ 0 ≤ a) :
    ∃ φ : σ(M, P) →P[ℂ] ℂ, φ.toPositiveLinearMap a < 0 := by
  -- need a funlike instance
  have h₁ : Convex ℝ {x : σ(M, P) | 0 ≤ x} := ConvexCone.positive ℝ σ(M, P) |>.convex
  have h₂ : LocallyConvexSpace ℝ σ(M, P) := inferInstance
  have h₃ : IsClosed {x : σ(M, P) | 0 ≤ x} := sorry
  obtain ⟨f, u, hfa, hf⟩ := geometric_hahn_banach_point_closed h₁ h₃ ha₂
  have hf_nonneg (x : σ(M, P)) (hx : 0 ≤ x) : 0 ≤ f x := by
    by_contra! hfx
    have hu : u < 0 := hf x hx |>.trans hfx
    have : 0 < u * (f x)⁻¹ := mul_pos_of_neg_of_neg hu (inv_neg''.mpr hfx)
    simpa [hfx.ne] using hf _ (smul_nonneg this.le hx)
  -- next we extend `f` to `ℂ`, then show the nonnegativity is preserved
  -- and that's our desired map. Piece of cake!
  sorry
