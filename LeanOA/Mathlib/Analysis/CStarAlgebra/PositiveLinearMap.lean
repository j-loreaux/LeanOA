import LeanOA.PositiveContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace PositiveLinearMap
variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂] (f : A₁ →ₚ[ℂ] A₂)

/-- Lift a positive linear map between C⋆-algebras to a positive continuous linear map. -/
def toPositiveContinuousLinearMap : A₁ →P[ℂ] A₂ where __ := f

@[simp] theorem toPositiveContinuousLinearMap_apply (x : A₁) :
    f.toPositiveContinuousLinearMap x = f x := rfl
@[simp] theorem toPositiveContinuousLinearMap_zero :
    (0 : A₁ →ₚ[ℂ] A₂).toPositiveContinuousLinearMap = 0 := rfl
@[simp] lemma toPositiveContinuousLinearMap_id :
    (PositiveLinearMap.id ℂ A₁).toPositiveContinuousLinearMap = .id ℂ A₁ := rfl

/-- Lift a positive linear map between C⋆-algebras to a continuous linear map. -/
abbrev toContinuousLinearMap : A₁ →L[ℂ] A₂ := f.toPositiveContinuousLinearMap.toContinuousLinearMap

theorem toContinuousLinearMap_apply (x : A₁) : f.toContinuousLinearMap x = f x := rfl
@[simp] theorem toContinuousLinearMap_zero : (0 : A₁ →ₚ[ℂ] A₂).toContinuousLinearMap = 0 := rfl
@[simp] theorem toLinearMap_toContinuousLinearMap :
    f.toContinuousLinearMap.toLinearMap = f.toLinearMap := rfl
@[simp] lemma toContinuousLinearMap_id :
    (PositiveLinearMap.id ℂ A₁).toContinuousLinearMap = .id ℂ A₁ := rfl

instance : CoeTC (A₁ →ₚ[ℂ] A₂) (A₁ →L[ℂ] A₂) := ⟨toContinuousLinearMap⟩

end PositiveLinearMap
