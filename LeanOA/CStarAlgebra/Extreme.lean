import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.LinearAlgebra.Complex.Module
import LeanOA.Mathlib.Misc
import Mathlib.Algebra.Group.Idempotent
import LeanOA.Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import LeanOA.Mathlib.Analysis.CStarAlgebra.GelfandDuality

open Set Metric Complex CFC
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
  letI := spectralOrder A
  letI := spectralOrderedRing A
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

-- what is the right generality for this? everything I try keeps timing out
-- move to appropriate file after generalizing it
lemma quasispectrum.norm_le_norm_of_mem {a : A} {x} (hx : x ∈ quasispectrum ℝ a) : ‖x‖ ≤ ‖a‖ :=
  (spectrum.norm_le_norm_of_mem ((Unitization.quasispectrum_eq_spectrum_inr ℝ a).symm ▸ hx)).trans
    (by simp [Unitization.norm_def])

theorem star_self_conjugate_eq_self_of_mem_extremePoints_closedUnitBall {a : A}
    (ha : a ∈ extremePoints ℝ (closedBall 0 1)) : a * star a * a = a := by
  /- Suppose `a` is an extreme point of the closed unit ball. Then we want to show that
  `a * star a * a = a`. It suffices to show `a * |a| = a`. -/
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
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
        have := x.le_norm_self.trans (by grw [quasispectrum.norm_le_norm_of_mem hx, norm_abs, ha])
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

private theorem eq_zero_of_eq_sub_of_mem_extremePoints_closedUnitBall {x a b : A}
    (hx : x ∈ extremePoints ℝ (closedBall 0 1))
    (hb : a = b - b * (star x * x) - (x * star x) * b + (x * star x) * b * (star x * x)) :
    a = 0 := by
  simpa using eq_zero_of_eq_sub_of_mem_closedBall_of_mem_extremePoints_closedUnitBall
    hx (inv_norm_smul_mem_unitClosedBall a) (b := ‖a‖⁻¹ • b)
    (by simp [← mul_assoc, smul_mul_assoc, mul_smul_comm, sub_sub, ← smul_sub, ← smul_add, hb])

open CStarAlgebra Filter Topology in
theorem CStarAlgebra.mul_ofExtremePtOne {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1))
    (a : A) : a * (star x * x + x * star x - x * star x * star x * x) = a := by
  let := spectralOrder A
  let := spectralOrderedRing A
  let u := increasingApproximateUnit A
  have h : ∀ t : A, t - t * (star x * x) - (x * star x) * t + (x * star x) * t * (star x * x) = 0 :=
    fun t ↦ eq_zero_of_eq_sub_of_mem_extremePoints_closedUnitBall hx rfl
  have overall := (((u.tendsto_mul_left a).sub
    (.const_mul a (u.tendsto_mul_right (star x * x)))).sub
    (.const_mul a (u.tendsto_mul_left (x * star x)))).add
    (.mul_const (star x * x) (u.tendsto_mul_left (a * (x * star x))))
  have (x_1 : A) : a * x_1 - a * (x_1 * (star x * x)) - a * (x * star x * x_1) +
      a * (x * star x) * x_1 * (star x * x) = 0 := by
    simp only [← mul_sub, mul_assoc, ← mul_add] at *
    exact mul_eq_zero_of_right a (h x_1)
  symm
  rw [← sub_eq_zero]
  have := by simpa [this] using overall
  simp [mul_add, mul_sub, mul_assoc] at *
  grind

@[simp] theorem star_mem_extremePoints_closedBall_zero_iff {A : Type*} [NonUnitalSeminormedRing A]
    [StarRing A] [NormedStarGroup A] [Module ℝ A] [StarModule ℝ A] {x : A} (c : ℝ) :
    star x ∈ extremePoints ℝ (closedBall 0 c) ↔ x ∈ extremePoints ℝ (closedBall 0 c) := by
  suffices ∀ x : A, x ∈ extremePoints ℝ (closedBall 0 c) → star x ∈ extremePoints ℝ (closedBall 0 c)
    from ⟨by simpa using this (star x), this x⟩
  clear x
  refine fun x hx ↦ ⟨by simpa using hx.1, fun y hy z hz ⟨α, β, hα, hβ, hαβ, hxyz⟩ ↦ ?_⟩
  rw [eq_star_iff_eq_star, eq_comm] at hxyz ⊢
  apply @hx.2 _ (by simpa using hy) (star z) (by simpa using hz) ⟨star α, star β, ?_⟩
  simp [← hxyz, hα, hβ, hαβ]

theorem CStarAlgebra.ofExtremePtOne_mul {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1))
    (a : A) : (star x * x + x * star x - x * star x * star x * x) * a = a := by
  have := CStarAlgebra.mul_ofExtremePtOne (x := star x) (a := star a) (hx := by simpa)
  rw [← star_inj]
  simp at *
  grind [star_add, ← star_zero, star_mul, star_sub]

/-- The ring structure given an extreme point of the closed unit ball on a non-unital
C⋆-algebra. Only an implementation for `CStarAlgebra.ofExtremePt`. -/
abbrev CStarAlgebra.ringOfExtremePt {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    Ring A where
  one := star x * x + x * star x - x * star x * star x * x
  one_mul y := ofExtremePtOne_mul hx y
  mul_one y := mul_ofExtremePtOne hx y

lemma CStarAlgebra.ofExtremePt_one_def {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    have := CStarAlgebra.ringOfExtremePt hx
    1 = star x * x + x * star x - x * star x * star x * x := rfl

/-- Upgrade a non-unital C⋆-algebra to a unital C⋆-algebra, given there exists an
extreme point of the closed unit ball. -/
abbrev CStarAlgebra.ofExtremePt {x : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) :
    CStarAlgebra A where
  __ := ‹NonUnitalCStarAlgebra A›
  __ := CStarAlgebra.ringOfExtremePt hx
  __ := Algebra.ofModule smul_mul_assoc mul_smul_comm

end nonUnital
