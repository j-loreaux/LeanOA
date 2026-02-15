import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]

/-- Lift a positive linear map between C⋆-algebras to a continuous linear map. -/
def PositiveLinearMap.toContinuousLinearMap (φ : A₁ →ₚ[ℂ] A₂) : A₁ →L[ℂ] A₂ :=
  { φ with cont := map_continuous φ }

@[simp] theorem PositiveLinearMap.toContinuousLinearMap_apply (φ : A₁ →ₚ[ℂ] A₂) (x : A₁) :
    φ.toContinuousLinearMap x = φ x := rfl
