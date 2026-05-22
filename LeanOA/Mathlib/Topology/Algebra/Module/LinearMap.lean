import Mathlib.Topology.Algebra.Module.LinearMap

namespace LinearMap

variable {S R₂ R₃ M M₂ M₃ : Type*} [CommSemiring S] [Semiring R₂] [Semiring R₃]
    {σ : R₂ →+* R₃} [AddCommMonoid M] [AddCommMonoid M₂] [AddCommGroup M₃] [Module S M]
    [Module R₂ M₂] [Module R₃ M₃] [Module S M₃] [TopologicalSpace M₂]
    [TopologicalSpace M₃] [SMulCommClass R₃ S M₃]
    [ContinuousConstSMul S M₃] [ContinuousAdd M₃] (B : M →ₗ[S] M₂ →ₛₗ[σ] M₃)
    (hB : ∀ x, Continuous (B x))

/-- Upgrade a bilinear map `B : M →ₗ[S] M₂ →ₛₗ[σ] M₃` to a linear map into continuous semilinear
  maps `M →ₗ[S] M₂ →SL[σ] M₃`. -/
noncomputable def toCSLMRight : M →ₗ[S] M₂ →SL[σ] M₃ :=
  letI e : (M₂ →SL[σ] M₃) ≃ₗ[S] (ContinuousLinearMap.coeLMₛₗ σ).range :=
    .ofInjective (ContinuousLinearMap.coeLMₛₗ σ) fun _ _ ↦ by simp [DFunLike.ext_iff]
  letI B' : M →ₗ[S] (ContinuousLinearMap.coeLMₛₗ σ).range :=
    B.codRestrict _ (fun x ↦ ⟨⟨B x, hB x⟩, rfl⟩)
  LinearEquiv.arrowCongr (LinearEquiv.refl S M) e.symm B'

lemma coeLM_toCSLMRight_apply (x : M) : B.toCSLMRight hB x = B x := by
  simp [← ContinuousLinearMap.coeLMₛₗ_apply (S₃ := S) σ, LinearMap.toCSLMRight]

@[simp] lemma coe_toCSLMRight (x : M) : ⇑(B.toCSLMRight hB x) = B x := by
  congrm($(B.coeLM_toCSLMRight_apply hB x))

end LinearMap
