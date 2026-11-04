module

public import LeanOA.CStarAlgebra.IsStarOrtho
public import LeanOA.CStarAlgebra.NormAddAlgebraMap
public import LeanOA.CStarAlgebra.Corner.Basic

@[expose] public section

/-! # Norm estimates for the decomposition of a C⋆-algebra by a projection

Let `p` and `q` be star-orthogonal projections in a C⋆-algebra `A`. This file collects some norm
estimates for elements of the "off-diagonal corner" `p * A * q`, which are used to show that this
corner is ultraweakly closed in a W⋆-algebra (see Sakai 1.7.6–1.7.8, and the treatment in
arXiv:2009.05825, Lemma 5.3.6).
-/

-- do we really not have these?
attribute [local grind =] star_mul star_add star_neg star_smul star_sub star_one star_zero star_star

-- we need a small grind set for non-unital rings
attribute [local grind =] mul_assoc add_mul mul_add smul_mul_assoc mul_smul_comm smul_smul
  sub_mul mul_sub

-- only use in the simplifying direction
attribute [local grind =>] IsIdempotentElem.mul_mul_self IsIdempotentElem.mul_self_mul
  IsIdempotentElem.eq

open scoped ComplexStarModule StarRing
open Filter Complex

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace IsStarProjection

variable {p : A} (hp : IsStarProjection p)
include hp

attribute [bound_forward] IsStarProjection.norm_le

/-- If, for some constant `C`, `‖x + c • p‖ ≤ √(C + ‖c‖ ^ 2)` for every `c : ℂ`, then
`p * x * p = 0`. -/
lemma mul_mul_eq_zero_of_norm_add_smul_le {x : A} (C : ℝ)
    (h : ∀ c : ℂ, ‖x + c • p‖ ≤ √(C + ‖c‖ ^ 2)) : p * x * p = 0 := by
  /- In the corner `p * A * p`, which is a C⋆-algebra with unit `p`, the compression
  `p * x * p` satisfies the hypotheses of `eq_zero_of_norm_add_algebraMap_le_norm_add`, since
  `√(C + ‖c‖ ^ 2) - ‖c‖ → 0` as `‖c‖ → ∞`. -/
  rw [← hp.coe_toCorner (R := ℂ) x, Corner.coe_eq_zero]
  refine eq_zero_of_norm_add_algebraMap_le_norm_add
    (tendsto_sqrt_add_sq_norm_sub_norm_cobounded C) (.of_forall fun c ↦ ?_)
  have hxp : p * x * p + c • p = p * (x + c • p) * p := by grind
  rw [add_sub_cancel, ← Corner.norm_coe, Corner.coe_add, Corner.coe_algebraMap, coe_toCorner, hxp]
  grw [norm_mul₃_le, hp.norm_le, one_mul, hp.norm_le, mul_one, h c]

variable {q : A} (hq : IsStarProjection q) (hpq : p ⋆⟂ q)
include hq hpq

/-- If `y` is in the closed unit ball, then `‖p * y * q + c • p‖ ≤ √(1 + ‖c‖ ^ 2)`. -/
lemma norm_mul_mul_add_smul_le {y : A} (hy : ‖y‖ ≤ 1) (c : ℂ) :
    ‖p * y * q + c • p‖ ≤ √(1 + ‖c‖ ^ 2) := by
  have hqp := hpq.mul_eq_zero' hq.isSelfAdjoint
  set x := p * y * q with hx_def
  have hx : ‖x‖ ≤ 1 := by grw [hx_def, norm_mul₃_le]; bound
  have hxp : x * p = 0 := by simp [x, mul_assoc, hqp]
  have hpx : p * star x = 0 := by grind [congr(star $hxp)]
  have hz : (x + c • p) * star (x + c • p) = x * star x + (star c * c) • p := by grind
  rw [Real.le_sqrt (norm_nonneg _) (by positivity), sq, ← CStarRing.norm_self_mul_star, hz]
  refine norm_add_le _ _ |>.trans <| add_le_add ?_ ?_
  · rw [CStarRing.norm_self_mul_star]
    simpa using mul_le_mul hx hx (norm_nonneg _) zero_le_one
  · rw [norm_smul, norm_mul, norm_star, ← sq]
    exact mul_le_of_le_one_right (by positivity) hp.norm_le

/-- If `y` is in the closed unit ball, then `‖p * y * q + c • q‖ ≤ √(1 + ‖c‖ ^ 2)`. -/
lemma norm_mul_mul_add_smul_le' {y : A} (hy : ‖y‖ ≤ 1) (c : ℂ) :
    ‖p * y * q + c • q‖ ≤ √(1 + ‖c‖ ^ 2) := by
  have := hq.norm_mul_mul_add_smul_le hp hpq.symm (y := star y) (by simpa using hy) (star c)
  rwa [← norm_star, star_add, star_mul, star_mul, star_smul, star_star,
    hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_star, ← mul_assoc,
    RCLike.star_def, RCLike.norm_conj] at this

/-- If `y` is in the closed unit ball and `b` lies in the corner `q * A * p`, then
`‖p * y * q + b‖ ≤ max 1 ‖b‖`. -/
lemma norm_mul_mul_add_le_max {y : A} (hy : ‖y‖ ≤ 1) {b : A} (hb : q * b * p = b) :
    ‖p * y * q + b‖ ≤ max 1 ‖b‖ := by
  /- `p * y * q` and `q * b * p` are star-orthogonal, so the norm of their sum is the maximum of
  their norms. -/
  have := (hpq.mul_mul hpq.symm y b).norm_add
  rw [hb] at this
  rw [this]
  gcongr
  grw [norm_mul₃_le]
  bound

end IsStarProjection
