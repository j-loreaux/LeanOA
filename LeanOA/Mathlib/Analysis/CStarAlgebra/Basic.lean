import Mathlib.Analysis.CStarAlgebra.Basic

theorem IsStarProjection.norm_le {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (e : A) (he : IsStarProjection e) : ‖e‖ ≤ 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  rw [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  simp

namespace Unitary
variable {A : Type*} (R : Type*) [NormedRing A] [StarRing A] [CStarRing A]
  [Ring R] [Module R A] [SMulCommClass R A A]

/-- Left multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulLeftLinearIsometryEquiv (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearMap := LinearMap.mulLeft R (u : A)
  invFun := LinearMap.mulLeft R (star u : A)
  left_inv _ := by simp [← mul_assoc]
  right_inv _ := by simp [← mul_assoc]
  norm_map' _ := CStarRing.norm_coe_unitary_mul _ _

@[simp] lemma mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    mulLeftLinearIsometryEquiv R u x = u * x := rfl

lemma symm_mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    (mulLeftLinearIsometryEquiv R u).symm x = star u * x := rfl

@[simp] lemma symm_mulLeftLinearIsometryEquiv (u : unitary A) :
    (mulLeftLinearIsometryEquiv R u).symm = mulLeftLinearIsometryEquiv R (star u) := by ext; rfl

end Unitary
