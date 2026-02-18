import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Extreme
import LeanOA.Mathlib.Misc
import LeanOA.Mathlib.LinearAlgebra.Complex.Module

open Set Metric
open scoped ComplexStarModule

@[simp]
lemma Set.extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    Set.extremePoints ℝ (Icc a b) = {a, b} := by
  ext x
  rw [convex_Icc .. |>.mem_extremePoints_iff_convex_diff]
  constructor
  · intro ⟨h₁, h₂⟩
    have := eq_endpoints_or_mem_Ioo_of_mem_Icc h₁
    suffices x ∉ Ioo a b by grind
    intro hx
    have := h₂.isPreconnected.Icc_subset (a := a) (b := b) (by grind) (by grind)
    grind
  · simp only [mem_insert_iff, mem_singleton_iff, mem_Icc]
    rintro (rfl | rfl)
    · simpa using ⟨hab, convex_Ioc ..⟩
    · simpa using ⟨hab, convex_Ico ..⟩

@[nontriviality]
lemma Set.extremePoints_eq_self {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [Subsingleton E] (A : Set E) :
    Set.extremePoints 𝕜 A = A :=
  subset_antisymm extremePoints_subset fun _ h ↦ ⟨h, fun _ _ _ _ _ ↦ Subsingleton.elim ..⟩

open Complex
lemma cfc_re_id {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a] :
    cfc (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' ℂ a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

open Complex
lemma cfc_im_id {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a] :
    cfc (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfc (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add .., cfc_const_mul .., cfc_re_id] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

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

-- what is the right generality for this?
lemma quasispectrum.norm_le_norm_of_mem {a : A} {x} (hx : x ∈ quasispectrum ℝ a) : ‖x‖ ≤ ‖a‖ :=
  (spectrum.norm_le_norm_of_mem ((Unitization.quasispectrum_eq_spectrum_inr ℝ a).symm ▸ hx)).trans
    (by simp [Unitization.norm_def])

-- replace with the `cfc_pull` tactic
private lemma cfcₙ_polynomial_aux (a : A) (α β γ : ℝ) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ (fun x ↦ α * x + β * x ^ 2 + γ * x ^ 3) a = α • a + β • (a * a) + γ • (a * a * a) := by
  simp only [pow_three', sq]
  repeat rw [cfcₙ_add (fun _ ↦ _) (fun _ ↦ _)]
  repeat rw [cfcₙ_const_mul _ (fun _ ↦ _)]
  repeat rw [cfcₙ_mul (fun _ ↦ _) (fun _ ↦ _), cfcₙ_id' ℝ a]

theorem isIdempotentElem_star_mul_self_of_mem_extremePoints_closedUnitBall
    [PartialOrder A] [StarOrderedRing A] {a : A} (ha : a ∈ extremePoints ℝ (closedBall 0 1)) :
    IsIdempotentElem (star a * a) := by
  suffices a * star a * a = a by grind [IsIdempotentElem]
  suffices (1 / 2 : ℝ) • (a + a * star a * a) = a by
    rwa [one_div, inv_smul_eq_iff₀ (by simp), two_smul, add_right_inj] at this
  obtain ⟨ha, h⟩ := ha
  simp only [mem_closedBall, dist_zero_right] at ha h
  have (x : ℝ) (hx : x ∈ quasispectrum ℝ (star a * a)) : 0 ≤ x ∧ x ≤ 1 := by
    refine ⟨quasispectrum_nonneg_of_nonneg _ (by simp) _ hx, le_trans (Real.le_norm_self _) ?_⟩
    grw [quasispectrum.norm_le_norm_of_mem hx, CStarRing.norm_star_mul_self, ha, one_mul]
  refine @h _ ?_ ((1 / 2 : ℝ) • ((3 : ℝ) • a - a * star a * a)) ?_ ⟨1 / 2, 1 / 2, ?_⟩
  · rw [← sq_le_one_iff₀ (by simp), sq, ← CStarRing.norm_star_mul_self]
    calc _ = ‖cfcₙ (fun x : ℝ ↦ 1 / 4 * x * (x + 1) ^ 2) (star a * a)‖ := ?_
      _ ≤ _ := by
        refine norm_cfcₙ_le fun y hy ↦ ?_
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by simp) (this y hy).1) (sq_nonneg _))]
        grw [this y hy |>.2] <;> grind
    congr
    ring_nf
    simp_rw [mul_comm _ (_ / _ : ℝ)]
    rw [cfcₙ_polynomial_aux (star a * a)]
    -- wow this is an annoying proof
    simp only [one_div, smul_add, star_add, star_smul, star_mul, mul_add, add_mul]
    simp only [smul_mul_smul, mul_assoc]
    norm_num
    simp only [one_div, add_assoc, add_right_inj]
    ring_nf
    rw [← add_assoc, ← add_smul]
    grind
  · rw [← sq_le_one_iff₀ (by simp), sq, ← CStarRing.norm_star_mul_self]
    calc _ = ‖cfcₙ (fun x : ℝ ↦ 1 / 4 * x * (x - 3) ^ 2) (star a * a)‖ := ?_
      _ ≤ _ := by
        refine norm_cfcₙ_le fun y hy ↦ ?_
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by simp) (this y hy).1) (sq_nonneg _)),
          mul_assoc, one_div_mul_eq_div, div_le_one (by positivity), ← sub_nonpos]
        calc _ = (y - 1) ^ 2 * (y - 4) := by ring
          _ ≤ _ := by nlinarith [this y hy]
    congr
    ring_nf
    simp_rw [mul_comm _ (_ / _ : ℝ)]
    rw [cfcₙ_polynomial_aux (star a * a)]
    -- again annoying proof
    simp only [one_div, smul_sub, smul_smul, star_sub, star_smul, star_mul, mul_sub, sub_mul]
    simp only [smul_mul_smul, mul_assoc, sub_eq_add_neg, neg_add_rev, neg_neg]
    norm_num
    simp only [one_div, add_assoc, add_right_inj]
    rw [add_comm, add_assoc, add_comm, add_left_inj, ← neg_smul, ← add_smul]
    norm_num
  simp only [one_div, inv_pos, smul_add, smul_smul, smul_sub, add_add_sub_cancel, ← add_smul]
  grind [one_smul]

open NNReal in
theorem quasispectrum_star_mul_self_subset_of_mem_extremePoints_closedUnitBall
    [PartialOrder A] [StarOrderedRing A] {a : A} (ha : a ∈ extremePoints ℝ≥0 (closedBall 0 1)) :
    quasispectrum ℝ≥0 (star a * a) ⊆ {0, 1} := by
  have : quasispectrum ℝ≥0 (star a * a) = Real.toNNReal '' quasispectrum ℝ (star a * a) := by
    refine (QuasispectrumRestricts.image ?_).symm
    exact nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp (star_mul_self_nonneg a) |>.2
  grw [this, image_subset_iff, preimage,
    (isIdempotentElem_star_mul_self_of_mem_extremePoints_closedUnitBall ?_).quasispectrum_subset]
  · simp [Set.subset_def]
  sorry

end nonUnital
