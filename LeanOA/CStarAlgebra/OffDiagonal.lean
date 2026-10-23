module

public import LeanOA.CFC
public import LeanOA.Ultraweak.OrderClosed
public import Mathlib.Algebra.Star.StarProjection

@[expose] public section

/-! # Norm estimates for the decomposition of a C⋆-algebra by a projection

Let `p` and `q` be orthogonal projections in a unital C⋆-algebra `A` with `p + q = 1`. This file
collects some norm estimates for elements of the "off-diagonal corner" `p * A * q`, which are used
to show that this corner is ultraweakly closed in a W⋆-algebra (see Sakai 1.7.6–1.7.8, and the
treatment in arXiv:2009.05825, Lemma 5.3.6).
-/

open scoped ComplexStarModule
open Filter Complex

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma norm_mul₃_le_one {a b c : A} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b * c‖ ≤ 1 :=
  calc ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul₃_le
    _ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

namespace IsStarProjection

variable {p : A} (hp : IsStarProjection p)
include hp

/-- A selfadjoint element `a` of the corner `p * A * p` satisfies `a ≤ ‖a‖ • p`. -/
lemma le_norm_smul_of_mul_mul_eq {a : A} (ha : IsSelfAdjoint a) (hpa : p * a * p = a) :
    a ≤ ‖a‖ • p :=
  calc a = star p * a * p := by rw [hp.isSelfAdjoint.star_eq, hpa]
    _ ≤ star p * algebraMap ℝ A ‖a‖ * p :=
      star_left_conjugate_le_conjugate ha.le_algebraMap_norm_self p
    _ = ‖a‖ • p := by
      rw [hp.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
        smul_mul_assoc, hp.isIdempotentElem.eq]

/-- A selfadjoint element `a` of the corner `p * A * p` satisfies `-(‖a‖ • p) ≤ a`. -/
lemma neg_norm_smul_le_of_mul_mul_eq {a : A} (ha : IsSelfAdjoint a) (hpa : p * a * p = a) :
    -(‖a‖ • p) ≤ a := by
  have := hp.le_norm_smul_of_mul_mul_eq ha.neg (by rw [mul_neg, neg_mul, hpa])
  rwa [norm_neg, neg_le] at this

variable {q : A} (hq : IsStarProjection q) (hpq : p * q = 0)
include hq hpq

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_eq_zero_of_mul_eq_zero : q * p = 0 := by
  simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $hpq)

omit [PartialOrder A] [StarOrderedRing A] in
/-- If `y` is in the closed unit ball, then `‖p * y * q + c • p‖ ≤ √(1 + ‖c‖ ^ 2)`. -/
lemma norm_mul_mul_add_smul_le {y : A} (hy : ‖y‖ ≤ 1) (c : ℂ) :
    ‖p * y * q + c • p‖ ≤ √(1 + ‖c‖ ^ 2) := by
  have hqp := hp.mul_eq_zero_of_mul_eq_zero hq hpq
  set x := p * y * q
  have hx : ‖x‖ ≤ 1 := norm_mul₃_le_one hp.norm_le hy hq.norm_le
  have hxp : x * p = 0 := by simp [x, mul_assoc, hqp]
  have hpx : p * star x = 0 := by
    simp [x, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, ← mul_assoc, hpq]
  have hz : (x + c • p) * star (x + c • p) = x * star x + (star c * c) • p := by
    simp only [star_add, star_smul, hp.isSelfAdjoint.star_eq, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, hxp, hpx, smul_zero, hp.isIdempotentElem.eq, smul_smul, add_zero, zero_add]
  rw [Real.le_sqrt (norm_nonneg _) (by positivity), sq, ← CStarRing.norm_self_mul_star, hz]
  refine norm_add_le _ _ |>.trans <| add_le_add ?_ ?_
  · rw [CStarRing.norm_self_mul_star]
    simpa using mul_le_mul hx hx (norm_nonneg _) zero_le_one
  · rw [norm_smul, norm_mul, norm_star, ← sq]
    exact mul_le_of_le_one_right (by positivity) hp.norm_le

omit [PartialOrder A] [StarOrderedRing A] in
/-- If `y` is in the closed unit ball, then `‖p * y * q + c • q‖ ≤ √(1 + ‖c‖ ^ 2)`. -/
lemma norm_mul_mul_add_smul_le' {y : A} (hy : ‖y‖ ≤ 1) (c : ℂ) :
    ‖p * y * q + c • q‖ ≤ √(1 + ‖c‖ ^ 2) := by
  have hqp := hp.mul_eq_zero_of_mul_eq_zero hq hpq
  have := hq.norm_mul_mul_add_smul_le hp hqp (y := star y) (by simpa using hy) (star c)
  rwa [← norm_star, star_add, star_mul, star_mul, star_smul, star_star,
    hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_star, ← mul_assoc,
    RCLike.star_def, RCLike.norm_conj] at this

variable (hpq₁ : p + q = 1)
include hpq₁

omit hpq in
/-- If `w` is a selfadjoint element of the corner `p * A * p` such that
`‖w + t • p‖ ≤ √(1 + t ^ 2)` for every real `t`, then `w = 0`. -/
lemma eq_zero_of_norm_add_smul_le {w : A} (hsa : IsSelfAdjoint w) (hw : p * w * p = w)
    (h : ∀ t : ℝ, ‖w + t • p‖ ≤ √(1 + t ^ 2)) : w = 0 := by
  nontriviality A
  /- First we show `‖w + t‖ ≤ √(1 + t ^ 2)` for every real `t`. Indeed, `w + t = a + t • q`,
  where `a := w + t • p` lies in the corner `p * A * p`, so `-m ≤ w + t ≤ m` with
  `m := √(1 + t ^ 2)`, since both `‖a‖` and `|t|` are at most `m`. -/
  have key (t : ℝ) : ‖w + algebraMap ℝ A t‖ ≤ √(1 + t ^ 2) := by
    set m := √(1 + t ^ 2)
    set a := w + t • p
    have ha : IsSelfAdjoint a := hsa.add ((IsSelfAdjoint.all t).smul hp.isSelfAdjoint)
    have hpa : p * a * p = a := by
      simp [a, mul_add, add_mul, hw, hp.isIdempotentElem.eq]
    have ham : ‖a‖ ≤ m := h t
    have htm : |t| ≤ m := Real.abs_le_sqrt (by linarith)
    have heq : w + algebraMap ℝ A t = a + t • q := by
      rw [Algebra.algebraMap_eq_smul_one, ← hpq₁]
      simp only [a, smul_add, add_assoc]
    have hm : algebraMap ℝ A m = m • p + m • q := by
      rw [Algebra.algebraMap_eq_smul_one, ← hpq₁, smul_add]
    have h₁ : w + algebraMap ℝ A t ≤ algebraMap ℝ A m := by
      rw [heq, hm]
      refine add_le_add ?_ (smul_le_smul_of_nonneg_right ((le_abs_self t).trans htm) hq.nonneg)
      exact (hp.le_norm_smul_of_mul_mul_eq ha hpa).trans <|
        smul_le_smul_of_nonneg_right ham hp.nonneg
    have h₂ : -algebraMap ℝ A m ≤ w + algebraMap ℝ A t := by
      rw [heq, hm, neg_add]
      refine add_le_add ?_ ?_
      · exact (neg_le_neg (smul_le_smul_of_nonneg_right ham hp.nonneg)).trans
          (hp.neg_norm_smul_le_of_mul_mul_eq ha hpa)
      · rw [← neg_smul]
        exact smul_le_smul_of_nonneg_right ((neg_le_neg htm).trans (neg_abs_le t)) hq.nonneg
    have := IsSelfAdjoint.norm_le_max_of_le_of_le h₂ h₁ (hsa.add (.algebraMap A (.all t)))
    rwa [norm_neg, max_self, norm_algebraMap', Real.norm_of_nonneg (Real.sqrt_nonneg _)] at this
  /- Every element `c` of the spectrum satisfies `|c| + n ≤ √(1 + n ^ 2)` for every `n : ℕ`,
  and hence `c = 0`. -/
  refine CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) w (fun c hc ↦ ?_) hsa
  rw [Set.mem_singleton_iff, ← abs_eq_zero]
  refine le_antisymm ?_ (abs_nonneg c)
  refine ge_of_tendsto' (tendsto_sqrt_one_add_sq_sub_self_atTop.comp tendsto_natCast_atTop_atTop)
    fun n ↦ ?_
  rw [Function.comp_apply, le_sub_iff_add_le]
  refine hsa.max_norm_add_sub_algebraMap_ge c hc n n.cast_nonneg |>.trans <| max_le (key n) ?_
  simpa [sub_eq_add_neg] using key (-n)

omit hpq in
/-- If `‖x + c • p‖ ≤ √(1 + ‖c‖ ^ 2)` for every `c : ℂ`, then `p * x * p = 0`. -/
lemma mul_mul_eq_zero_of_norm_add_smul_le {x : A}
    (h : ∀ c : ℂ, ‖x + c • p‖ ≤ √(1 + ‖c‖ ^ 2)) : p * x * p = 0 := by
  have hpp := hp.isIdempotentElem.eq
  set z := p * x * p
  have hz : p * z * p = z := by
    simp only [z, ← mul_assoc, hpp]
    rw [mul_assoc (p * x) p p, hpp]
  have hz' (c : ℂ) : ‖z + c • p‖ ≤ √(1 + ‖c‖ ^ 2) := by
    have : z + c • p = p * (x + c • p) * p := by
      simp [z, mul_add, add_mul, hpp]
    rw [this]
    refine (h c).trans' ?_
    calc ‖p * (x + c • p) * p‖ ≤ ‖p‖ * ‖x + c • p‖ * ‖p‖ := norm_mul₃_le
      _ ≤ 1 * ‖x + c • p‖ * 1 := by gcongr <;> exact hp.norm_le
      _ = ‖x + c • p‖ := by ring
  /- The real and imaginary parts of `z` lie in the corner `p * A * p` and satisfy the hypotheses
  of `eq_zero_of_norm_add_smul_le`. -/
  have hstar : p * star z * p = star z := by
    simpa [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc] using congr(star $hz)
  have hre : (ℜ z : A) = 0 := by
    refine hp.eq_zero_of_norm_add_smul_le hq hpq₁ (ℜ z).2 ?_ fun t ↦ ?_
    · simp [realPart_apply_coe, mul_add, add_mul, hz, hstar]
    · simpa [sq_abs, hp.isSelfAdjoint.coe_realPart] using
        (realPart.norm_le (z + (t : ℂ) • p)).trans (hz' t)
  have him : (ℑ z : A) = 0 := by
    refine hp.eq_zero_of_norm_add_smul_le hq hpq₁ (ℑ z).2 ?_ fun t ↦ ?_
    · simp [imaginaryPart_apply_coe, mul_sub, sub_mul, hz, hstar]
    · simpa [sq_abs, mul_smul, imaginaryPart_I_smul, hp.isSelfAdjoint.coe_realPart] using
        (imaginaryPart.norm_le (z + (I * t) • p)).trans (hz' (I * t))
  rw [← realPart_add_I_smul_imaginaryPart z, hre, him, smul_zero, add_zero]

omit hpq₁ in
/-- If `y` is in the closed unit ball and `b` lies in the corner `q * A * p`, then
`‖p * y * q + b‖ ≤ max 1 ‖b‖`. -/
lemma norm_mul_mul_add_le_max {y : A} (hy : ‖y‖ ≤ 1) {b : A} (hb : q * b * p = b)
    (hpq₁ : p + q = 1) :
    ‖p * y * q + b‖ ≤ max 1 ‖b‖ := by
  nontriviality A
  have hqp := hp.mul_eq_zero_of_mul_eq_zero hq hpq
  set x := p * y * q
  set m := max 1 ‖b‖
  have hx : ‖x‖ ≤ 1 := norm_mul₃_le_one hp.norm_le hy hq.norm_le
  have hpb : p * b = 0 := by rw [← hb]; simp [← mul_assoc, hpq]
  have hbp : star b * p = 0 := by
    rw [← hb]; simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_assoc, hqp]
  have hxq : x * q = x := by simp [x, mul_assoc, hq.isIdempotentElem.eq]
  /- `star (x + b) * (x + b) = star x * x + star b * b`, which lies between `0` and
  `m ^ 2 • q + m ^ 2 • p = algebraMap ℝ A (m ^ 2)`. -/
  have hz : star (x + b) * (x + b) = star x * x + star b * b := by
    have h₁ : star x * b = 0 := by
      simp [x, star_mul, mul_assoc, hp.isSelfAdjoint.star_eq, hpb]
    have h₂ : star b * x = 0 := by simp [x, ← mul_assoc, hbp]
    simp [add_mul, mul_add, h₁, h₂]
  have hxx : star x * x ≤ m ^ 2 • q := by
    have hqx : q * (star x * x) * q = star x * x := by
      have h : q * star x = star x := by
        rw [← hq.isSelfAdjoint.star_eq, ← star_mul, hxq]
      rw [show q * (star x * x) * q = (q * star x) * (x * q) by simp only [mul_assoc], h, hxq]
    refine (hq.le_norm_smul_of_mul_mul_eq (.star_mul_self x) hqx).trans <|
      smul_le_smul_of_nonneg_right ?_ hq.nonneg
    rw [CStarRing.norm_star_mul_self, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hx.trans (le_max_left _ _)) 2
  have hbb : star b * b ≤ m ^ 2 • p := by
    have hpbb : p * (star b * b) * p = star b * b := by
      have hbp' : b * p = b := by rw [← hb]; simp [mul_assoc, hp.isIdempotentElem.eq]
      have h : p * star b = star b := by
        rw [← hp.isSelfAdjoint.star_eq, ← star_mul, hbp']
      rw [show p * (star b * b) * p = (p * star b) * (b * p) by simp only [mul_assoc], h, hbp']
    refine (hp.le_norm_smul_of_mul_mul_eq (.star_mul_self b) hpbb).trans <|
      smul_le_smul_of_nonneg_right ?_ hp.nonneg
    rw [CStarRing.norm_star_mul_self, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
  have hle : star (x + b) * (x + b) ≤ algebraMap ℝ A (m ^ 2) := by
    rw [hz, Algebra.algebraMap_eq_smul_one, ← hpq₁, smul_add, add_comm (m ^ 2 • p)]
    exact add_le_add hxx hbb
  have hm : 0 ≤ m := le_max_of_le_left zero_le_one
  rw [← sq_le_sq₀ (norm_nonneg _) hm, sq, ← CStarRing.norm_star_mul_self]
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity) (star_mul_self_nonneg _)).mpr hle

end IsStarProjection
