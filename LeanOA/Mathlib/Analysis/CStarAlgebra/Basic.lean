import Mathlib.Analysis.CStarAlgebra.Basic

theorem IsStarProjection.norm_le {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (e : A) (he : IsStarProjection e) : ‖e‖ ≤ 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  rw [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  simp
