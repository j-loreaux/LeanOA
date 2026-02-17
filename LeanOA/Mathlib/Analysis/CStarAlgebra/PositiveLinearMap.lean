import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace PositiveLinearMap
variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂] (f : A₁ →ₚ[ℂ] A₂)

/-- Lift a positive linear map between C⋆-algebras to a continuous linear map. -/
def toContinuousLinearMap : A₁ →L[ℂ] A₂ := { f with cont := map_continuous f }

@[simp] theorem toContinuousLinearMap_apply (x : A₁) : f.toContinuousLinearMap x = f x := rfl

@[simp] theorem toLinearMap_toContinuousLinearMap :
    f.toContinuousLinearMap.toLinearMap = f.toLinearMap := rfl

end PositiveLinearMap
