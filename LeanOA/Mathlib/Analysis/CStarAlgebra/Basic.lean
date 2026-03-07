import Mathlib.Analysis.CStarAlgebra.Basic

theorem IsStarProjection.norm_le {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (e : A) (he : IsStarProjection e) : ‖e‖ ≤ 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  rw [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  simp

namespace Unitary
variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
  [Ring R] [Module R A] [SMulCommClass R A A]

variable (R A) in
/-- Left multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulLeftLinearIsometryEquiv : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { toLinearMap := LinearMap.mulLeft R (u : A)
      invFun := LinearMap.mulLeft R (star u : A)
      left_inv _ := by simp [← mul_assoc]
      right_inv _ := by simp [← mul_assoc]
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp] lemma mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    mulLeftLinearIsometryEquiv R A u x = u * x := rfl

lemma symm_mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    (mulLeftLinearIsometryEquiv R A u).symm x = star u * x := rfl

@[simp] lemma symm_mulLeftLinearIsometryEquiv (u : unitary A) :
    (mulLeftLinearIsometryEquiv R A u).symm = mulLeftLinearIsometryEquiv R A (star u) := by ext; rfl

lemma mulLeftLinearIsometryEquiv_trans_mulLeftLinearIsometryEquiv (u v : unitary A) :
    (mulLeftLinearIsometryEquiv R A v).trans (mulLeftLinearIsometryEquiv R A u) =
    mulLeftLinearIsometryEquiv R A (u * v) := map_mul _ _ _ |>.symm

lemma mulLeftLinearIsometryEquiv_mul_apply (u v : unitary A) (x : A) :
    mulLeftLinearIsometryEquiv R A (u * v) x =
      mulLeftLinearIsometryEquiv R A u (mulLeftLinearIsometryEquiv R A v x) := by simp

@[simp] lemma toLinearMap_mulLeftLinearIsometryEquiv (u : unitary A) :
    (mulLeftLinearIsometryEquiv R A u).toLinearMap = LinearMap.mulLeft R (u : A) := rfl

end Unitary
