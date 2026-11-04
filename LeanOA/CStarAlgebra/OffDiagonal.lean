module

public import LeanOA.CStarAlgebra.IsStarOrtho
public import LeanOA.Ultraweak.OrderClosed
public import Mathlib.Analysis.CStarAlgebra.Unitization

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

/-- The unital case of `IsStarProjection.eq_zero_of_norm_add_smul_le`. -/
private lemma eq_zero_of_norm_add_smul_le_of_unital {B : Type*} [CStarAlgebra B] {p : B}
    (hp : IsStarProjection p) {w : B} (hsa : IsSelfAdjoint w) (hw : p * w * p = w)
    (h : ∀ t : ℝ, ‖w + t • p‖ ≤ √(1 + t ^ 2)) : w = 0 := by
  /- We first show `‖w + t‖ ≤ √(1 + t ^ 2)` for every real `t`. Indeed,
  `w + t = (w + t • p) + t • (1 - p)` is a sum of star-orthogonal elements, the first of norm at
  most `√(1 + t ^ 2)` and the second of norm at most `|t|`. -/
  have key (t : ℝ) : ‖w + algebraMap ℝ B t‖ ≤ √(1 + t ^ 2) := by
    have hortho : (w + t • p) ⋆⟂ (t • (1 - p)) := by
      refine .smul_right ?_ t
      rw [hp.one_sub.isSelfAdjoint.isStarOrtho_iff]
      grind
    have heq : w + algebraMap ℝ B t = (w + t • p) + t • (1 - p) := by
      rw [Algebra.algebraMap_eq_smul_one, smul_sub]
      abel
    rw [heq, hortho.norm_add]
    refine max_le (h t) ?_
    grw [norm_smul, hp.one_sub.norm_le, mul_one, Real.norm_eq_abs]
    exact Real.abs_le_sqrt (by linarith)
  exact hsa.eq_zero_of_norm_add_algebraMap_le key

variable {p : A} (hp : IsStarProjection p)
include hp

attribute [bound_forward] IsStarProjection.norm_le

/-- If `w` is a selfadjoint element of the corner `p * A * p` such that
`‖w + t • p‖ ≤ √(1 + t ^ 2)` for every real `t`, then `w = 0`. -/
lemma eq_zero_of_norm_add_smul_le {w : A} (hsa : IsSelfAdjoint w) (hw : p * w * p = w)
    (h : ∀ t : ℝ, ‖w + t • p‖ ≤ √(1 + t ^ 2)) : w = 0 := by
  /- We pass to the unitization, where the unital case applies. -/
  have hp' : IsStarProjection (p : Unitization ℂ A) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have := eq_zero_of_norm_add_smul_le_of_unital hp' (hsa.inr ℂ)
    (by simp [← Unitization.inr_mul, hw]) fun t ↦ by
      simpa [← Unitization.inr_smul, ← Unitization.inr_add, Unitization.norm_inr] using h t
  exact Unitization.inr_injective (R := ℂ) (by simpa using this)

/-- If `‖x + c • p‖ ≤ √(1 + ‖c‖ ^ 2)` for every `c : ℂ`, then `p * x * p = 0`. -/
lemma mul_mul_eq_zero_of_norm_add_smul_le {x : A}
    (h : ∀ c : ℂ, ‖x + c • p‖ ≤ √(1 + ‖c‖ ^ 2)) : p * x * p = 0 := by
  set z := p * x * p
  have hz : p * z * p = z := by grind
  have hz' (c : ℂ) : ‖z + c • p‖ ≤ √(1 + ‖c‖ ^ 2) := by
    have : z + c • p = p * (x + c • p) * p := by grind
    grw [this, norm_mul₃_le, hp.norm_le, one_mul, hp.norm_le, mul_one, h c]
  /- The real and imaginary parts of `z` lie in the corner `p * A * p` and satisfy the hypotheses
  of `eq_zero_of_norm_add_smul_le`. -/
  have hstar : p * star z * p = star z := by
    simpa [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc] using congr(star $hz)
  have hre : (ℜ z : A) = 0 := by
    refine hp.eq_zero_of_norm_add_smul_le (ℜ z).2 ?_ fun t ↦ ?_
    · simp [realPart_apply_coe, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, hz, hstar]
    · simpa [sq_abs, hp.isSelfAdjoint.coe_realPart] using
        (realPart.norm_le (z + (t : ℂ) • p)).trans (hz' t)
  have him : (ℑ z : A) = 0 := by
    refine hp.eq_zero_of_norm_add_smul_le (ℑ z).2 ?_ fun t ↦ ?_
    · simp [imaginaryPart_apply_coe, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, hz, hstar]
    · simpa [sq_abs, mul_smul, imaginaryPart_I_smul, hp.isSelfAdjoint.coe_realPart] using
        (imaginaryPart.norm_le (z + (I * t) • p)).trans (hz' (I * t))
  rw [← realPart_add_I_smul_imaginaryPart z, hre, him, smul_zero, add_zero]

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
