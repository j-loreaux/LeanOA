import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.LinearAlgebra.Complex.Module
import LeanOA.Mathlib.Misc

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
section Functions

variable {X R : Type*} [TopologicalSpace X] [NormedRing R] [IsDomain R]

-- A better way to do this would be to prove that the norm of a bounded
-- continuous function agrees with the norm of the real-valued function where
-- you compose pointwise with the norm. That should simplify the argument a
-- bit I think, at the cost of developing more API (which is probably worthwhile).

open BoundedContinuousFunction in
/-- If the product of bounded continuous functions is zero, then the norm of their sum is the
maximum of their norms. -/
lemma BoundedContinuousFunction.norm_add_eq_max {f g : X →ᵇ R} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  have hfg : ∀ x, f x = 0 ∨ g x = 0 := by
    simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' (x : X) : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by
    obtain (h | h) := hfg x <;> simp [h]
  apply le_antisymm
  · rw [norm_le (by positivity)]
    intro x
    rw [hfg']
    apply max_le <;> exact norm_coe_le_norm _ x |>.trans (by simp)
  · apply max_le
    all_goals
      rw [norm_le (by positivity)]
      intro x
      grw [← (f + g).norm_coe_le_norm x, hfg']
      simp

open BoundedContinuousFunction in
lemma ContinuousMap.norm_add_eq_max [CompactSpace X] {f g : C(X, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using congr($h x)
  simpa using BoundedContinuousFunction.norm_add_eq_max h

end Functions

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

open scoped CStarAlgebra in
open Unitization in
lemma CommCStarAlgebra.norm_add_eq {a b : A} (h : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom ℂ A
  have hf : Isometry f := gelfandTransform_isometry _ |>.comp isometry_inr
  have h0 : f 0 = 0 := by simp [f]
  simp_rw [← hf.norm_map_of_map_zero h0, show f (a + b) = f a + f b by simp [f]]
  exact ContinuousMap.norm_add_eq_max <| by simpa [f] using congr(f $h)

open NonUnitalStarAlgebra in
lemma IsSelfAdjoint.norm_add_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {a b : A} (hab : a * b = 0) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let S : NonUnitalStarSubalgebra ℂ A := (adjoin ℂ {a, b}).topologicalClosure
  have hS : IsClosed (S : Set A) := (adjoin ℂ {a, b}).isClosed_topologicalClosure
  have hab' : a * b = b * a := by
    rw [hab, eq_comm]; simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  let _ : NonUnitalCommRing (adjoin ℂ {a, b}) :=
    adjoinNonUnitalCommRingOfComm ℂ (by grind) (by grind [IsSelfAdjoint.star_eq])
  let _ : NonUnitalCommRing S := (adjoin ℂ {a, b}).nonUnitalCommRingTopologicalClosure mul_comm
  let _ : NonUnitalCommCStarAlgebra S := { }
  let c : S := ⟨a, subset_closure <| subset_adjoin _ _ <| by grind⟩
  let d : S := ⟨b, subset_closure <| subset_adjoin _ _ <| by grind⟩
  exact CommCStarAlgebra.norm_add_eq (a := c) (b := d) (h := by ext; simpa)

-- still needs a better name, but will probably be private anyway
theorem eq_zero_of_sub_of_mem_closedBall_of_mem_extremePoints_closedUnitBall
    {x a b : A} (hx : x ∈ extremePoints ℝ (closedBall 0 1)) (ha : a ∈ closedBall 0 1)
    (hb : a = b - b * (star x * x) - (x * star x) * b + (x * star x) * b * (star x * x)) :
    a = 0 := by
  have hP := isStarProjection_star_mul_self_of_mem_extremePoints_closedUnitBall hx
  set p := star x * x with hp
  have hxa : star x * a = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← CStarRing.norm_star_mul_self]
    simp [hb, mul_add, mul_sub, add_mul, sub_mul]
    grind [hP.isIdempotentElem.eq] => ac
  have hax : star a * x = 0 := by
    rw [← star_star x, ← star_mul, ← star_zero]
    exact star_inj.mpr hxa
  have hpa : p * (star a * a) = 0 := by
    simp only [hb, mul_add, mul_sub]
    grind [hP.isIdempotentElem.eq]
  have : (star x + star a) * (x + a) = p + star a * a := by
    simp [hp, mul_add, add_mul, hax, hxa]
  have : ‖p + star a * a‖ = ‖x + a‖ * ‖x + a‖ := by
    rw [← this, ← star_add, CStarRing.norm_star_mul_self]
  have hmax : ‖p + star a * a‖ ≤ 1 := by
    rw [IsSelfAdjoint.norm_add_eq hpa (.star_mul_self x) (.star_mul_self a), sup_le_iff]
    constructor
    · have : ‖x‖ ≤ 1 := by simpa using mem_of_mem_inter_left hx
      simpa [hp, CStarRing.norm_star_mul_self] using mul_le_mul this (by simpa) (norm_nonneg x)
    · have : ‖a‖ ≤ 1 := by simpa using ha
      simpa [CStarRing.norm_star_mul_self] using mul_le_mul this (by simpa) (norm_nonneg a)
  have : ‖x + a‖ ≤ 1 := sq_le_one_iff₀ (by positivity) |>.mp (by grind)
  have : ‖x - a‖ ≤ 1 := by
    rw [← sq_le_one_iff₀ (by positivity)]
    simp [sq, ← CStarRing.norm_star_mul_self, star_sub, sub_mul, mul_sub, hax, hxa, ← hp, hmax]
  exact add_eq_left.mp <| @hx.2 (x + a) (by simpa) (x - a) (by simpa)
    ⟨2⁻¹, 2⁻¹, by simp [smul_add, smul_sub, ← add_smul, ← one_div]⟩

end nonUnital
