import LeanOA.Mathlib.Algebra.Star.StarProjection
import LeanOA.Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import LeanOA.Mathlib.Analysis.CStarAlgebra.Basic
import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import LeanOA.Mathlib.Analysis.CStarAlgebra.GelfandDuality
import LeanOA.Mathlib.LinearAlgebra.Complex.Module
import LeanOA.CFC

import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

open Set Metric Complex CFC CStarAlgebra Unitization
open scoped ComplexStarModule

/-! # Extreme points of the closed unit ball in C⋆-algebras

This file contains results on the extreme points of the closed unit ball in (unital) C⋆-algebras.
In particular, we show that a C⋆-algebra is unital if and only if there exists an extreme point
of the closed unit ball.

## References
[Sakai], [Pedersen], [Takesaki], [Kadison], [Murphy]
-/

-- move to...?
@[simp]
lemma Set.extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    Set.extremePoints ℝ (Icc a b) = {a, b} := by
  ext x
  rw [convex_Icc .. |>.mem_extremePoints_iff_convex_diff]
  constructor
  · intro ⟨h₁, h₂⟩
    suffices x ∉ Ioo a b by grind
    intro hx
    have := h₂.isPreconnected.Icc_subset (a := a) (b := b) (by grind) (by grind)
    grind
  · rintro (rfl | rfl)
    · simpa using ⟨hab, convex_Ioc ..⟩
    · simpa using ⟨hab, convex_Ico ..⟩

lemma CStarAlgebra.one_mem_extremePoints_closedUnitBall {A : Type*} [CStarAlgebra A] :
    1 ∈ extremePoints ℝ (closedBall (0 : A) 1) := by
  nontriviality A
  /- Suppose that `1` is a convex combination of `x` and `y`. Then, since `1` is self
  adjoint, it is also a combination of their real and imaginary parts, which we
  call `a` and `b`. Moreover, `b` is a linear polynomial in the variable `a`, so we
  may write it as the continuous functional calculus applied to the appropriate
  function of `a`. -/
  refine ⟨by simp, fun x hx y hy hxy ↦ ?_⟩
  let +nondep (eq := ha') a : A := ℜ x
  let +nondep (eq := hb') b : A := ℜ y
  simp only [mem_closedBall, dist_zero_right] at hx hy
  have ha : ‖a‖ ≤ 1 := by simpa [ha'] using realPart.norm_le _ |>.trans hx
  have hb : ‖b‖ ≤ 1 := by simpa [hb'] using realPart.norm_le _ |>.trans hy
  obtain ⟨c₁, hc₁, c₂, hc₂, hc, hcab⟩ := by simpa [openSegment] using hxy
  replace hcab : c₁ • a + c₂ • b = 1 := by simpa [ha', hb'] using congr((ℜ $hcab : A))
  have : b = c₂⁻¹ • 1 - c₂⁻¹ • c₁ • a := by
    simpa [inv_smul_smul₀ hc₂.ne', eq_sub_iff_add_eq'] using congr(c₂⁻¹ • $hcab)
  rw [this, ← cfc_id' ℝ a, ← cfc_one ℝ a, ← cfc_smul .., ← cfc_smul .., ← cfc_smul ..,
    ← cfc_sub .., ← cfc_smul .., ← cfc_add .., cfc_eq_cfc_iff_eqOn] at hcab
  /- By passing to functions, we will show that `a = 1`. In particular, the constant
  function `1` on the `ℝ`-spectrum of `a` is a convex combination of functions (one of
  which is the identity) which are bounded in absolute value by `1`. Since `1 : ℝ` is
  extreme in `Icc (-1) 1`, we conclude that these functions must be `1` on the
  spectrum of `a`. -/
  obtain rfl : a = 1 := by
    refine CFC.eq_one_of_spectrum_subset_one (R := ℝ) a fun r hr ↦ ?_
    have h1_mem : (1 : ℝ) ∈ openSegment ℝ r (c₂⁻¹ - c₂⁻¹ * c₁ * r) :=
      ⟨c₁, c₂, hc₁, hc₂, hc, by simpa [mul_assoc] using hcab hr⟩
    have key : (1 : ℝ) ∈ extremePoints ℝ (Icc (-1) 1) := by simp
    simp only [mem_singleton_iff]
    refine mem_extremePoints_iff_left.mp key |>.2 _ ?_ _ ?_ h1_mem
    · simpa [abs_le] using (spectrum.norm_le_norm_of_mem hr).trans ha
    · suffices c₂⁻¹ - c₂⁻¹ * c₁ * r ∈ spectrum ℝ b by
        simpa [abs_le] using (spectrum.norm_le_norm_of_mem this).trans hb
      rw [this, ← Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, sub_eq_add_neg]
      rwa [add_comm c₂⁻¹, spectrum.add_mem_add_iff, ← spectrum.neg_eq, Set.neg_mem_neg, smul_smul,
        spectrum.smul_eq_smul _ _ (nonempty_of_mem hr), ← smul_eq_mul _ r,
        Set.smul_mem_smul_set_iff₀ (by positivity)]
  /- Since `ℜ x = a = 1`, so too we conclude `ℜ y = b = 1`. -/
  obtain rfl : b = 1 := by
    simpa [← smul_assoc, ← sub_smul, (sub_eq_iff_eq_add.mpr hc.symm).symm, mul_sub, hc₂.ne']
  clear this hb ha hcab hb' hc hc₂ hc₁ c₁ c₂ hy hxy y
  /- Since `ℜ x = 1`, the real and imaginary parts of `x` commute, so `x` is normal. It
  then suffices to show that `ℑ x = 0`. -/
  have hx' : IsStarNormal x := by simp [isStarNormal_iff_commute_realPart_imaginaryPart, ← ha']
  suffices (ℑ x : A) = 0 by rw [← realPart_add_I_smul_imaginaryPart x, ← ha', this]; simp
  let := spectralOrder A
  let := spectralOrderedRing A
  /- Note that `‖1 + (ℑ x) ^ 2‖ = ‖(ℜ x) ^ 2 + (ℑ x) ^ 2‖ = ‖star x * x‖ = ‖x‖ ^ 2 ≤ 1`.
  Therefore, `1 + (ℑ x) ^ 2 ≤ 1`, so `(ℑ x) ^ 2 ≤ 0`. Since `(ℑ x) ^ 2` is clearly nonnegative,
  we conclude that it is zero, and hence so also `ℑ x = 0`, as desired. -/
  rw [← sq_le_one_iff₀ (by positivity), sq, ← CStarRing.norm_star_mul_self,
    star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← ha', mul_one, ← sq,
    CStarAlgebra.norm_le_one_iff_of_nonneg _ (add_nonneg zero_le_one (ℑ x).2.sq_nonneg)] at hx
  rw [← norm_eq_zero, ← sq_eq_zero_iff, ← IsSelfAdjoint.norm_mul_self (ℑ x).2, ← sq, norm_eq_zero]
  exact le_antisymm (by simpa using hx) (ℑ x).2.sq_nonneg

section nonUnital
variable {A : Type*} [NonUnitalCStarAlgebra A]

-- `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric`
alias quasispectrum.norm_le_norm_of_mem :=
  NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le

theorem star_self_conjugate_eq_self_of_mem_extremePoints_closedUnitBall {a : A}
    (ha : a ∈ extremePoints ℝ (closedBall 0 1)) : a * star a * a = a := by
  /- Suppose `a` is an extreme point of the closed unit ball. Then we want to show that
  `a * star a * a = a`. It suffices to show `a * |a| = a`. -/
  let := spectralOrder A
  let := spectralOrderedRing A
  suffices a * abs a = a by rw [mul_assoc, ← abs_mul_abs, ← mul_assoc, this, this]
  obtain ⟨ha, h⟩ := ha
  simp only [mem_closedBall, dist_zero_right] at ha h
  /- Using the extremity of `a`, it suffices to show that `2 • |a| - |a| * |a|` is in the
  closed unit ball since `2⁻¹ • (2 • |a| - |a| * |a|) + 2⁻¹ • (a * |a|) = a`
  (and clearly `a * |a|` is in the closed unit ball since `a` is). -/
  refine @h _ ?_ ((2 : ℝ) • a - a * abs a) ?_ ⟨2⁻¹, 2⁻¹, by simp [smul_sub, ← two_mul]⟩
  · grw [norm_mul_le, norm_abs, ha, one_mul]
  · /- To show this inequality (i.e., `‖2 • a - a * |a|‖ ≤ 1`), we first
    show equality with `‖2 • |a| - |a| * |a|‖` (using the C⋆-identity), and then pass to the
    continuous functional calculus where we then use `norm_cfcₙ_le` to show the rest
    (using the fact that the elements in the quasispectrum of `|a|`
    are bounded between `0` and `1`). -/
    calc
      _ = ‖(2 : ℝ) • abs a - abs a * abs a‖ := by
        simp_rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
        simp only [star_sub, star_smul, star_mul, mul_sub, mul_smul_comm, sub_mul, smul_mul_assoc]
        simp [abs_nonneg a |>.star_eq, mul_assoc, ← mul_assoc _ a, ← abs_mul_abs]
      _ = ‖cfcₙ (fun x : ℝ ↦ 2 * x - x * x) (abs a)‖ := by
        rw [cfcₙ_sub _ _, cfcₙ_const_mul _ _, cfcₙ_mul _ _, cfcₙ_id' ℝ (abs a)]
      _ ≤ _ := norm_cfcₙ_le fun x hx ↦ by
        have := x.le_norm_self.trans (by grw [quasispectrum.norm_le_norm_of_mem _ hx, norm_abs, ha])
        rw [Real.norm_of_nonneg] <;> nlinarith [quasispectrum_nonneg_of_nonneg _ (by simp) _ hx]

attribute [local grind .] IsSelfAdjoint.star_mul_self IsIdempotentElem IsSelfAdjoint.mul_star_self
attribute [local grind] IsStarProjection

theorem isStarProjection_star_mul_self_of_mem_extremePoints_closedUnitBall
    {a : A} (ha : a ∈ extremePoints ℝ (closedBall 0 1)) : IsStarProjection (star a * a) := by
  grind [star_self_conjugate_eq_self_of_mem_extremePoints_closedUnitBall ha]

theorem isStarProjection_self_mul_star_of_mem_extremePoints_closedUnitBall
    {a : A} (ha : a ∈ extremePoints ℝ (closedBall 0 1)) : IsStarProjection (a * star a) := by
  grind [star_self_conjugate_eq_self_of_mem_extremePoints_closedUnitBall ha]

variable {A : Type*} [NonUnitalCStarAlgebra A]

private theorem eq_zero_of_eq_sub_of_mem_closedBall_of_mem_extremePoints_closedUnitBall
    {x a b : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) (ha : a ∈ closedBall 0 1)
    (hb : a = b - b * (star x * x) - (x * star x) * b + (x * star x) * b * (star x * x)) :
    a = 0 := by
  have hP := isStarProjection_star_mul_self_of_mem_extremePoints_closedUnitBall hx
  have hQ := isStarProjection_self_mul_star_of_mem_extremePoints_closedUnitBall hx
  set p := star x * x with hp
  have hxa : star x * a = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← CStarRing.norm_star_mul_self]
    simp [hb, mul_add, mul_sub, add_mul, sub_mul]
    grind
  have hax : star a * x = 0 := by simpa [star_mul] using congr(star $hxa)
  have hpa : p * (star a * a) = 0 := by
    simp only [hb, mul_add, mul_sub, star_add, star_sub, star_mul, add_mul, sub_mul]
    grind [star_star_mul x x]
  have : star (x + a) * (x + a) = p + star a * a := by simp [hp, mul_add, add_mul, hax, hxa]
  have : ‖p + star a * a‖ = ‖x + a‖ * ‖x + a‖ := by rw [← this, CStarRing.norm_star_mul_self]
  have hmax : ‖p + star a * a‖ ≤ 1 := by
    rw [IsSelfAdjoint.star_mul_self x |>.norm_add_eq_max hpa (.star_mul_self a), sup_le_iff, hp]
    simp only [CStarRing.norm_star_mul_self]
    grw [mem_closedBall_zero_iff.mp hx.1, mem_closedBall_zero_iff.mp ha, one_mul, and_self]
  have : ‖x + a‖ ≤ 1 := sq_le_one_iff₀ (by positivity) |>.mp <| by grind
  have : ‖x - a‖ ≤ 1 := sq_le_one_iff₀ (by positivity) |>.mp <| by
    simp [sq, ← CStarRing.norm_star_mul_self, sub_mul, mul_sub, hax, hxa, ← hp, hmax]
  exact add_eq_left.mp <| @hx.2 (x + a) (by simpa) (x - a) (by simpa)
    ⟨2⁻¹, 2⁻¹, by simp [smul_add, smul_sub, ← add_smul, ← one_div]⟩

open Filter Topology in
/-- When `x` is an extreme point of the closed unit ball in a non-unital C⋆-algebra,
then `star x * x + x * star x - x * star x * star x * x` is a right identity.
(See also `CStarAlgebra.ofExtremePtOne_mul` for the left identity.) -/
theorem CStarAlgebra.mul_ofExtremePtOne {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1))
    (a : A) : a * (star x * x + x * star x - x * star x * (star x * x)) = a := by
  let := spectralOrder A
  let := spectralOrderedRing A
  let u := approximateUnit A
  let hu := increasingApproximateUnit A
  let f (t : A) : A := t - t * (star x * x) - x * star x * t + x * star x * t * (star x * x)
  have h (t : A) : f t = 0 := by
    simpa using eq_zero_of_eq_sub_of_mem_closedBall_of_mem_extremePoints_closedUnitBall
      hx (inv_norm_smul_mem_unitClosedBall (f t)) (b := ‖f t‖⁻¹ • t)
      (by simp [← mul_assoc, smul_mul_assoc, mul_smul_comm, sub_sub, ← smul_sub, ← smul_add, f])
  have h_tendsto : Tendsto (fun t ↦ a * f t) u
      (𝓝 (a - a * (star x * x + x * star x - x * star x * (star x * x)))) := by
    conv => enter [1, t]; simp only [f]; rw [sub_add, sub_sub, add_sub, mul_sub]
    apply_rules [Tendsto.sub, Tendsto.add, hu.tendsto_mul_left, hu.tendsto_mul_right,
      Tendsto.mul_const, Tendsto.const_mul]
  simpa [h, sub_eq_zero, eq_comm (a := (0 : A)), eq_comm (a := a)] using h_tendsto

@[simp]
theorem star_mem_extremePoints_closedBall_zero_iff {A : Type*} [NonUnitalSeminormedRing A]
    [StarRing A] [NormedStarGroup A] [Module ℝ A] [StarModule ℝ A] {x : A} (c : ℝ) :
    star x ∈ extremePoints ℝ (closedBall 0 c) ↔ x ∈ extremePoints ℝ (closedBall 0 c) := by
  suffices ∀ x : A, x ∈ extremePoints ℝ (closedBall 0 c) → star x ∈ extremePoints ℝ (closedBall 0 c)
    from ⟨fun h ↦ star_star x ▸ this (star x) h, this x⟩
  refine fun x hx ↦ ⟨by simpa using hx.1, fun y hy z hz ⟨α, β, hα, hβ, hαβ, hxyz⟩ ↦ ?_⟩
  rw [eq_star_iff_eq_star, eq_comm] at hxyz ⊢
  apply @hx.2 _ (by simpa using hy) (star z) (by simpa using hz) ⟨star α, star β, ?_⟩
  simp [← hxyz, hα, hβ, hαβ]

/-- When `x` is an extreme point of the closed unit ball in a non-unital C⋆-algebra,
then `star x * x + x * star x - x * star x * star x * x` is a left identity.
(See also `CStarAlgebra.mul_ofExtremePtOne` for the right identity.) -/
theorem CStarAlgebra.ofExtremePtOne_mul {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1))
    (a : A) : (star x * x + x * star x - x * star x * (star x * x)) * a = a := by
  simpa [add_comm] using congr(star $(mul_ofExtremePtOne (x := star x) (by simpa) (star a)))

/-- The ring structure given an extreme point of the closed unit ball on a non-unital
C⋆-algebra. Only an implementation for `CStarAlgebra.ofExtremePt`. -/
abbrev CStarAlgebra.ringOfExtremePt {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    Ring A where
  one := star x * x + x * star x - x * star x * (star x * x)
  one_mul y := ofExtremePtOne_mul hx y
  mul_one y := mul_ofExtremePtOne hx y

lemma CStarAlgebra.ofExtremePt_one_def {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    letI := CStarAlgebra.ringOfExtremePt hx
    1 = star x * x + x * star x - x * star x * (star x * x) :=
  rfl

/-- Upgrade a non-unital C⋆-algebra to a unital C⋆-algebra, given there exists an
extreme point of the closed unit ball. -/
abbrev CStarAlgebra.ofExtremePt {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    CStarAlgebra A where
  __ := ‹NonUnitalCStarAlgebra A›
  __ := ringOfExtremePt hx
  __ := Algebra.ofModule smul_mul_assoc mul_smul_comm

-- `Mathlib.Algebra.Group.Idempotent`
attribute [grind =>] IsIdempotentElem.mul_mul_self IsIdempotentElem.mul_self_mul

/-- The set of star projections on a non-unital C⋆-algebra is exactly the extreme points of
the nonnegative closed unit ball. -/
theorem isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall
    [PartialOrder A] [StarOrderedRing A] {e : A} :
    IsStarProjection e ↔ e ∈ extremePoints ℝ {x : A | 0 ≤ x ∧ x ∈ closedBall 0 1} := by
  simp only [mem_closedBall, dist_zero_right, mem_extremePoints_iff_left, mem_setOf_eq, and_imp]
  refine ⟨fun he ↦ ⟨⟨he.nonneg, he.norm_le⟩,
    fun a ha ha1 b hb hb1 ⟨t, s, h0t, h0s, hts, hlin⟩ ↦ ?_⟩, fun ⟨⟨h1, h2⟩, h3⟩ ↦ ?_⟩
  · have : t • (e * ((1 - a : A⁺¹) * e)) + s • (e * ((1 - b) * e)) =
        (t + s) • e - e * (t • a + s • b) * e := by
      simp [smul_sub, sub_add_eq_add_sub, add_sub, ← add_smul, hts, sub_mul, mul_sub,
        he.inr.isIdempotentElem.eq, mul_add, add_mul, sub_sub, mul_assoc]
    have : ((t + s) • e - e * (t • a + s • b) * e : A⁺¹) = 0 := by
      simp [← inr_smul, ← inr_add, ← inr_mul, hts, hlin, he.isIdempotentElem.eq]
    have H {q : ℝ} {c : A} (hq : 0 < q) (h0c : 0 ≤ c) (hc1 : ‖c‖ ≤ 1) :
        0 ≤ q • (e * ((1 - c : A⁺¹) * e)) := by
      rw [← smul_zero q, smul_le_smul_iff_of_pos_left hq, ← mul_assoc]
      exact he.inr.isSelfAdjoint.conjugate_nonneg (sub_nonneg_of_le <|
        (norm_le_one_iff_of_nonneg (c : A⁺¹) (by simpa)).mp (by simpa [norm_inr]))
    have := le_add_iff_nonneg_right (t • (e * ((1 - a : A⁺¹) * e))) |>.mpr (H h0s hb hb1)
    have : e * ((1 - a : A⁺¹) * e) = 0 := by rw [← smul_eq_zero_iff_right h0t.ne']; grind
    have := he.conjugate_of_nonneg_of_le (a := t • a) (by positivity)
      (by simpa [hlin] using le_add_of_nonneg_right (a := t • a) (by positivity : 0 ≤ s • b))
    rw [mul_smul_comm, smul_mul_assoc] at this
    have h : e * (e - a * e) = 0 := by rw [← (inr_injective (R := ℂ)).eq_iff]; simpa [← one_sub_mul]
    rwa [mul_sub, ← mul_assoc, he.isIdempotentElem, h0t.ne'.isUnit.smul_left_cancel.mp this,
      sub_eq_zero, eq_comm] at h
  · have := calc
      0 ≤ (e : A⁺¹) * (2 - e) := by
        have : (e : A⁺¹) ≤ 1 := by
          rwa [← norm_inr (𝕜 := ℂ), norm_le_one_iff_of_nonneg _ (by simpa)] at h2
        apply Commute.mul_nonneg (by simpa) (by grw [sub_nonneg, this, one_le_two])
        simp [commute_iff_eq, mul_sub, sub_mul, mul_two, two_mul]
      _ = (((2 : ℝ) • e - e * e : A) : A⁺¹) := by simp [mul_sub, two_smul, mul_two]
    refine ⟨h3 _ (Commute.mul_nonneg h1 h1 rfl) ?_ ((2 : ℝ) • e - e * e) this.of_inr ?_
      ⟨2⁻¹, 2⁻¹, by simp [smul_sub, ← one_div, smul_smul]⟩, h1.isSelfAdjoint⟩
    · grw [norm_mul_le, h2, one_mul]
    · rw [← norm_inr (𝕜 := ℂ), norm_le_one_iff_of_nonneg _ this, ← sub_nonneg]
      calc 0 ≤ star (1 - e : A⁺¹) * (1 - e) := star_mul_self_nonneg _
        _ = _ := by simp [LE.le.star_eq, h1, mul_sub, sub_mul, two_smul, sub_sub, add_sub]

end nonUnital

section SelfAdjointUnitary

namespace Unitary
variable {A : Type*} (R : Type*) [NormedRing A] [StarRing A] [CStarRing A]
  [Ring R] [Module R A] [SMulCommClass R A A]

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

lemma mulLeftLinearIsometryEquiv_image_extremePoints_closedUnitBall [PartialOrder R]
    [IsOrderedRing R] (u : unitary A) :
    (mulLeftLinearIsometryEquiv R u) '' extremePoints R (closedBall 0 1) =
      extremePoints R (closedBall 0 1) := by
  rw [image_extremePoints, LinearIsometryEquiv.image_closedBall]
  simp

lemma coe_mem_extremePoints_closedUnitBall {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (u : unitary A) :
    (u : A) ∈ extremePoints ℝ (closedBall 0 1) := by
  rw [← mulLeftLinearIsometryEquiv_image_extremePoints_closedUnitBall ℝ u]
  exact ⟨1 , ⟨CStarAlgebra.one_mem_extremePoints_closedUnitBall, by simp⟩⟩

end Unitary

theorem isSelfAdjoint_unitary_mem_extremePoints_isSelfAdjoint_inter_extremePoints_closedUnitBall
    {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {u : A} (hu : IsSelfAdjoint u ∧ u ∈ unitary A) :
    u ∈ Set.extremePoints ℝ ({x | IsSelfAdjoint x} ∩ Metric.closedBall 0 1) := by
  refine inter_extremePoints_subset_extremePoints_of_subset (inter_subset_right)
    ⟨⟨hu.1, ?_⟩, by simpa using Unitary.coe_mem_extremePoints_closedUnitBall ⟨u, hu.2⟩⟩
  nontriviality A
  simp [hu]

lemma norm_sub_le_one_of_nonneg_le_one_nonneg_le_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {x y : A} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) : ‖x - y‖ ≤ 1 := by
  nontriviality A
  simpa [sub_eq_add_neg] using (IsSelfAdjoint.one _).neg.norm_le_max_of_le_of_le
    (by simpa using add_le_add hx.1 (neg_le_neg_iff.mpr hy.2))
    (add_le_add hx.2 (by simpa using neg_le_neg hy.1 : -y ≤ 0))

theorem isStarProjection_posPart_of_mem_extremePoints_isSelfAdjoint_and_mem_closedUnitBall
    {A : Type*} [NonUnitalCStarAlgebra A]
    {e : A} (he : e ∈ extremePoints ℝ {x | IsSelfAdjoint x ∧ x ∈ closedBall 0 1}) :
    IsStarProjection (e⁺ : A) := by
  let := spectralOrder A
  let := spectralOrderedRing A
  rw [isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall]
  refine ⟨⟨posPart_nonneg e, ?_⟩, fun x hx y hy ⟨α, β, hα, hβ, hαβ, h⟩ ↦ ?_⟩
  · grw [mem_closedBall_zero_iff, norm_posPart_le, mem_closedBall_zero_iff.mp he.1.2]
  have hpn := by simpa [sub_eq_iff_eq_add] using posPart_sub_negPart e he.1.1
  have (x : A) (hx : 0 ≤ x) (hx0 : x ∈ closedBall 0 1) : x - e⁻ ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, ← norm_inr (𝕜 := ℂ), inr_sub]
    refine norm_sub_le_one_of_nonneg_le_one_nonneg_le_one ?_ ?_
    · simp [hx, ← norm_le_one_iff_of_nonneg (x : A⁺¹), norm_inr, mem_closedBall_zero_iff.mp hx0]
    · simp only [inr_nonneg_iff, negPart_nonneg e, true_and]
      grw [← norm_le_one_iff_of_nonneg _ (negPart_nonneg e).inr, norm_inr, norm_negPart_le,
        mem_closedBall_zero_iff.mp he.1.2]
  have := he.2 ⟨hx.1.isSelfAdjoint.sub (negPart_nonneg e).isSelfAdjoint, this x hx.1 hx.2⟩
    ⟨hy.1.isSelfAdjoint.sub (negPart_nonneg e).isSelfAdjoint, this y hy.1 hy.2⟩
  refine hpn ▸ sub_eq_iff_eq_add.mp <| this ⟨α, β, hα, hβ, hαβ, ?_⟩
  simp [smul_sub, sub_add_sub_comm, ← add_smul, hαβ, sub_eq_iff_eq_add, ← hpn, h]

theorem isStarProjection_negPart_of_mem_extremePoints_isSelfAdjoint_and_mem_closedUnitBall
    {A : Type*} [NonUnitalCStarAlgebra A]
    {e : A} (he : e ∈ Set.extremePoints ℝ {x | IsSelfAdjoint x ∧ x ∈ closedBall 0 1}) :
    IsStarProjection (e⁻ : A) := by
  let := spectralOrder A
  let := spectralOrderedRing A
  rw [isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall]
  refine ⟨⟨negPart_nonneg e, ?_⟩, fun x hx y hy ⟨α, β, hα, hβ, hαβ, h⟩ ↦ ?_⟩
  · grw [mem_closedBall_zero_iff, norm_negPart_le, mem_closedBall_zero_iff.mp he.1.2]
  have hpn := by simpa [sub_eq_iff_eq_add' (c := e), ← sub_eq_iff_eq_add] using
    posPart_sub_negPart e he.1.1
  have (x : A) (hx : 0 ≤ x) (hx0 : x ∈ closedBall 0 1) : e⁺ - x ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, ← norm_neg, neg_sub, ← norm_inr (𝕜 := ℂ), inr_sub]
    refine norm_sub_le_one_of_nonneg_le_one_nonneg_le_one ?_ ?_
    · simp [hx, ← norm_le_one_iff_of_nonneg (x : A⁺¹), norm_inr, mem_closedBall_zero_iff.mp hx0]
    · simp only [inr_nonneg_iff, posPart_nonneg e, true_and]
      grw [← norm_le_one_iff_of_nonneg _ (posPart_nonneg e).inr, norm_inr, norm_posPart_le,
        mem_closedBall_zero_iff.mp he.1.2]
  have := he.2 ⟨(posPart_nonneg e).isSelfAdjoint.sub hx.1.isSelfAdjoint, this x hx.1 hx.2⟩
    ⟨(posPart_nonneg e).isSelfAdjoint.sub hy.1.isSelfAdjoint, this y hy.1 hy.2⟩
  rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, eq_comm, hpn] at this
  refine this ⟨α, β, hα, hβ, hαβ, ?_⟩
  simp [smul_sub, sub_add_sub_comm, ← add_smul, hαβ, ← hpn, h]

/-- The extreme points of the self-adjoint closed unit ball is exactly the set of self-adjoint
unitaries. -/
theorem mem_extremePoints_isSelfAdjoint_and_mem_closedUnitBall_iff_isSelfAdjoint_and_unitary
    {A : Type*} [CStarAlgebra A] {e : A} :
    e ∈ extremePoints ℝ {x | IsSelfAdjoint x ∧ x ∈ closedBall 0 1} ↔
      IsSelfAdjoint e ∧ e ∈ unitary A := by
  let := spectralOrder A
  let := spectralOrderedRing A
  refine ⟨fun he ↦ ⟨he.1.1, ?_⟩, fun he ↦ ?_⟩
  · rw [Unitary.mem_iff, he.1.1, and_self, ← posPart_sub_negPart e he.1.1]
    have h1 := isStarProjection_negPart_of_mem_extremePoints_isSelfAdjoint_and_mem_closedUnitBall he
    have h2 := isStarProjection_posPart_of_mem_extremePoints_isSelfAdjoint_and_mem_closedUnitBall he
    simp only [mul_sub, sub_mul, h2.isIdempotentElem.eq, negPart_mul_posPart, sub_zero,
      posPart_mul_negPart, h1.isIdempotentElem.eq, zero_sub, sub_neg_eq_add]
    rw [eq_comm, ← sub_eq_zero]
    set x := 1 - (e⁺ + e⁻)
    have hx : IsStarProjection x := (h2.add h1 (by simp)).one_sub
    refine add_eq_left.mp <| @he.2 (e + x) ⟨?_, ?_⟩ (e - x) ⟨?_, ?_⟩ ⟨2⁻¹, 2⁻¹, ?_⟩
    · simp [IsSelfAdjoint, he.1.1.star_eq, x, LE.le.star_eq, posPart_nonneg e, negPart_nonneg e]
    · grw [mem_closedBall_zero_iff, IsSelfAdjoint.norm_add_eq_max _ he.1.1 _,
        mem_closedBall_zero_iff.mp he.1.2, hx.norm_le, max_self]
      · rw [← posPart_sub_negPart e he.1.1]
        simp [x, mul_add, h1.isIdempotentElem.eq, h2.isIdempotentElem.eq, sub_eq_add_neg, add_mul]
      · exact IsSelfAdjoint.one _ |>.sub (h2.isSelfAdjoint.add h1.isSelfAdjoint)
    · simp [IsSelfAdjoint, he.1.1.star_eq, x, LE.le.star_eq, posPart_nonneg e, negPart_nonneg e]
    · grw [mem_closedBall_zero_iff, IsSelfAdjoint.norm_sub_eq_max _ he.1.1 _,
        mem_closedBall_zero_iff.mp he.1.2, hx.norm_le, max_self]
      · rw [← posPart_sub_negPart e he.1.1]
        simp [x, mul_add, h1.isIdempotentElem.eq, h2.isIdempotentElem.eq, sub_eq_add_neg, add_mul]
      · exact IsSelfAdjoint.one _ |>.sub (h2.isSelfAdjoint.add h1.isSelfAdjoint)
    simp [← one_div, smul_add, smul_sub, ← two_smul ℝ, smul_smul, mul_one_div_cancel]
  · refine inter_extremePoints_subset_extremePoints_of_subset inter_subset_right
      ⟨⟨he.1, ?_⟩, by simpa using Unitary.coe_mem_extremePoints_closedUnitBall ⟨e, he.2⟩⟩
    nontriviality A
    simp [he]

/- We can use the following to reduce NonUnital to Unital . -/
lemma nonunital_part {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {e : A} (he : e ∈ Set.extremePoints ℝ ({x | IsSelfAdjoint x} ∩ Metric.closedBall 0 1)) (x : A) :
    CFC.abs e * x = x ∧ x * CFC.abs e = x := by
  -- the earlier bits + my argument above
  sorry

end SelfAdjointUnitary
