module

public import LeanOA.Ultraweak.Basic
public import LeanOA.KreinSmulian
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

@[expose] public section

open scoped NNReal Ultraweak ComplexStarModule Topology
open Filter Complex

section KreinSmulian

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
variable [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P] [CompleteSpace P]
variable [Module ℝ≥0 M] [IsScalarTower ℝ≥0 𝕜 M]

/-- The Krein-Smulian theorem transferred from `WeakDual ℂ P` to `σ(M, P)`. This could
generalize trivially from `ℂ` to `RCLike 𝕜`. -/
protected lemma Ultraweak.krein_smulian_of_submodule (S : Submodule ℝ≥0 (σ(M, P)_𝕜))
    (hS : IsClosed ((S : Set (σ(M, P)_𝕜)) ∩ ofUltraweak ⁻¹' (Metric.closedBall (0 : M) 1))) :
    IsClosed (S : Set (σ(M, P)_𝕜)) := by
  have := (weakDualCLE 𝕜 M P).preimage_symm_preimage (S : Set (σ(M, P)_𝕜))
  rw [← this] at hS ⊢
  rw [ofUltraweak_preimage_closedBall, ← Set.preimage_inter] at hS
  apply (weakDualCLE 𝕜 M P).toHomeomorph.isClosed_preimage.mp at hS
  refine .preimage (map_continuous _) ?_
  simp only [map_zero] at hS
  exact krein_smulian_of_submodule
    (S.comap ((weakDualCLE 𝕜 M P).toLinearEquiv.symm.restrictScalars ℝ≥0 |>.toLinearMap)) hS

end KreinSmulian

variable {M P : Type*} [CStarAlgebra M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

lemma tendsto_sqrt_add_sq_sub_self_atTop (C : ℝ) :
    Tendsto (fun x : ℝ ↦ √(C + x ^ 2) - x) atTop (𝓝 0) := by
  /- For large `x`, `√(C + x ^ 2) - x = C / (√(C + x ^ 2) + x)`, and the denominator is at
  least `x`. -/
  have key : ∀ᶠ x in atTop, C / (√(C + x ^ 2) + x) = √(C + x ^ 2) - x := by
    filter_upwards [eventually_ge_atTop (|C| + 1)] with x hx
    have hx₀ : 0 < x := by linarith [abs_nonneg C]
    have hCx : 0 ≤ C + x ^ 2 := by nlinarith [neg_abs_le C]
    rw [div_eq_iff (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hx₀).ne']
    linear_combination -Real.sq_sqrt hCx
  refine .congr' key <| tendsto_const_nhds.div_atTop ?_
  exact tendsto_atTop_mono (fun _ ↦ le_add_of_nonneg_left (Real.sqrt_nonneg _)) tendsto_id

lemma IsSelfAdjoint.norm_add_I_smul_sq_of_commute {A : Type*}
    [NonUnitalCStarAlgebra A] {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hxy : Commute x y) :
    ‖x + I • y‖ ^ 2 = ‖x * x + y * y‖ := by
  simp [sq, ← CStarRing.norm_star_mul_self, hx.star_eq, hy.star_eq,
    ← sub_eq_add_neg, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm,
    hxy.eq, smul_sub, smul_smul, ← add_assoc]

lemma IsSelfAdjoint.norm_add_I_smul_le_of_commute {A : Type*}
    [NonUnitalCStarAlgebra A] {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hxy : Commute x y) :
    ‖x + I • y‖ ≤ √(‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [Real.le_sqrt (by positivity) (by positivity), hx.norm_add_I_smul_sq_of_commute hy hxy,
    ← hx.norm_mul_self, ← hy.norm_mul_self]
  exact norm_add_le ..

-- this lemma is poorly named, and maybe we should remove it entirely.
-- or else we could parametermize the lemma above with inequalities on `‖x‖` and `‖y‖`.
lemma IsSelfAdjoint.norm_isSelfAdjoint_add_I_smul_algebraMap
    {M : Type*} [CStarAlgebra M] {x : M} (hx : IsSelfAdjoint x)
    (hx₁ : ‖x‖ ≤ 1) (r : ℝ) :
    ‖x + I • algebraMap ℝ M r‖ ≤ √(1 + r ^ 2) := by
  nontriviality M
  apply hx.norm_add_I_smul_le_of_commute (.algebraMap M (.all r))
    (Algebra.commute_algebraMap_right r x) |>.trans
  simp only [norm_algebraMap', Real.norm_eq_abs, sq_abs]
  gcongr
  rwa [sq_le_one_iff₀ (by positivity)]

-- this lemma seems a bit too technical? Maybe it's useful though.
lemma IsSelfAdjoint.max_norm_add_sub_algebraMap_ge
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {x : A}
    (hx : IsSelfAdjoint x) (c : ℝ) (hc : c ∈ spectrum ℝ x) (r : ℝ) (hr : r ≥ 0) :
    |c| + r ≤ max ‖x + algebraMap ℝ A r‖ ‖x - algebraMap ℝ A r‖ := by
  obtain (hc' | hc') := le_total 0 c
  · apply le_max_of_le_left
    convert! norm_apply_le_norm_cfc (fun y : ℝ ↦ y + r) x hc using 1
    · simp [abs_of_nonneg (a := c + r) (by positivity), abs_of_nonneg hc']
    · rw [cfc_add .., cfc_const .., cfc_id' ..]
  · apply le_max_of_le_right
    convert! norm_apply_le_norm_cfc (fun y : ℝ ↦ -y + r) x hc using 1
    · rw [abs_of_nonpos hc', Real.norm_eq_abs, abs_of_nonneg]
      positivity [neg_nonneg.mpr hc']
    · rw [cfc_add _ (- ·) _, cfc_neg_id .., cfc_const .., norm_sub_rev]
      congr! 1
      abel

/-- A selfadjoint element `x` such that, for some constant `C`, `‖x + t‖ ≤ √(C + t ^ 2)` for
every real `t`, is zero. -/
lemma IsSelfAdjoint.eq_zero_of_norm_add_algebraMap_le
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {x : A} (hx : IsSelfAdjoint x)
    {C : ℝ} (h : ∀ t : ℝ, ‖x + algebraMap ℝ A t‖ ≤ √(C + t ^ 2)) : x = 0 := by
  /- Every element `c` of the spectrum satisfies `|c| + n ≤ √(C + n ^ 2)` for every `n : ℕ`,
  and hence `c = 0`. -/
  refine CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) x (fun c hc ↦ ?_) hx
  rw [Set.mem_singleton_iff, ← abs_eq_zero]
  refine le_antisymm ?_ (abs_nonneg c)
  refine ge_of_tendsto' ((tendsto_sqrt_add_sq_sub_self_atTop C).comp tendsto_natCast_atTop_atTop)
    fun n ↦ ?_
  rw [Function.comp_apply, le_sub_iff_add_le]
  refine hx.max_norm_add_sub_algebraMap_ge c hc n n.cast_nonneg |>.trans <| max_le (h n) ?_
  simpa [sub_eq_add_neg] using h (-n)

/-- An element `x` of a unital C⋆-algebra such that, for some constant `C`,
`‖x + c‖ ≤ √(C + ‖c‖ ^ 2)` for every `c : ℂ`, is zero. -/
lemma eq_zero_of_norm_add_algebraMap_le {A : Type*} [CStarAlgebra A] {x : A} {C : ℝ}
    (h : ∀ c : ℂ, ‖x + algebraMap ℂ A c‖ ≤ √(C + ‖c‖ ^ 2)) : x = 0 := by
  /- The real and imaginary parts of `x` satisfy the hypotheses of
  `IsSelfAdjoint.eq_zero_of_norm_add_algebraMap_le`. -/
  have hre : (ℜ x : A) = 0 := by
    refine (ℜ x).2.eq_zero_of_norm_add_algebraMap_le (C := C) fun t ↦ ?_
    simpa [Algebra.algebraMap_eq_smul_one, sq_abs, (IsSelfAdjoint.one (R := A)).coe_realPart] using
      (realPart.norm_le (x + algebraMap ℂ A t)).trans (h t)
  have him : (ℑ x : A) = 0 := by
    refine (ℑ x).2.eq_zero_of_norm_add_algebraMap_le (C := C) fun t ↦ ?_
    simpa [Algebra.algebraMap_eq_smul_one, sq_abs, mul_smul, imaginaryPart_I_smul,
      (IsSelfAdjoint.one (R := A)).coe_realPart] using
      (imaginaryPart.norm_le (x + algebraMap ℂ A (I * t))).trans (h (I * t))
  rw [← realPart_add_I_smul_imaginaryPart x, hre, him, smul_zero, add_zero]

namespace Ultraweak

set_option backward.isDefEq.respectTransparency false in
/-- The selfadjoint elements are closed in the ultraweak topology. -/
lemma isClosed_setOf_isSelfAdjoint : IsClosed {x : σ(M, P) | IsSelfAdjoint x} := by
  nontriviality σ(M, P)
  have : Nontrivial M := linearEquiv ℂ M P |>.symm.nontrivial
  /- By the Krein-Smulian theorem, it suffices to show that the set of
  selfadjoint elements in the closed unit ball is closed. -/
  apply Ultraweak.krein_smulian_of_submodule <|
    (selfAdjoint.submodule ℝ σ(M, P)).restrictScalars ℝ≥0
  /- take any filter within the closed unit ball of selfadjoint elements which is
  also contained within `𝓝 x`. We must show `x` is in the closed unit ball of
  selfadjoint elements. This is the filter equivalent of "let x_α be a net of
  selfadjoint elements of norm at most 1 converging to x. We show x is selfadjoint." -/
  rw [isClosed_iff_forall_filter]
  intro x l hl_neBot hl_sa hlx
  refine Set.mem_inter (?_ : IsSelfAdjoint x) ?mem_ball
  -- Since the closed unit ball is ultraweakly closed, `x` is in the closed unit ball.
  case mem_ball =>
    exact isClosed_iff_forall_filter.mp (isClosed_closedBall ℂ P (0 : M) 1)
      x l hl_neBot (by aesop) hlx
  /- To show `x` is self-adjoint, we show `ℑ x = 0`. By
  `IsSelfAdjoint.eq_zero_of_norm_add_algebraMap_le`, it suffices to show that
  `‖ℑ x + t‖ ≤ ‖x + I • t‖ ≤ √(1 + t ^ 2)` for every real `t`. -/
  refine .of_ofUltraweak ?_
  rw [← imaginaryPart_eq_zero_iff, ← ZeroMemClass.coe_eq_zero]
  refine (ℑ (ofUltraweak x)).2.eq_zero_of_norm_add_algebraMap_le (C := 1) fun t ↦ ?_
  trans ‖ofUltraweak x + I • algebraMap ℝ M t‖
  · convert! imaginaryPart.norm_le (ofUltraweak x + I • algebraMap ℝ M t) using 1
    simp [(IsSelfAdjoint.algebraMap M (.all t)).coe_realPart]
  /- `fun m : σ(M, P) ↦ m + I • t` stays within the closed ball of radius `√(1 + t ^ 2)`
  and converges to `x + I • t` along the filter `l`. -/
  have h₃ : Tendsto (fun m : σ(M, P) ↦ m + I • algebraMap ℝ σ(M, P) t) l
      (𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) √(1 + t ^ 2)) ⊓
        𝓝 (x + I • algebraMap ℝ σ(M, P) t)) := by
    refine tendsto_inf.mpr ⟨.mono_left ?_ hl_sa, .add_const _ hlx⟩
    simpa using fun x hx hx_norm ↦
      hx.ofUltraweak.norm_isSelfAdjoint_add_I_smul_algebraMap hx_norm t
  have := isClosed_iff_forall_filter.mp <| isClosed_closedBall ℂ P (0 : M) (√(1 + t ^ 2))
  simpa using this _ _ inferInstance (tendsto_inf.mp h₃ |>.1) (tendsto_inf.mp h₃ |>.2)

variable [PartialOrder M] [StarOrderedRing M]

set_option backward.isDefEq.respectTransparency false in
open Pointwise in
/-- The nonnegative elements are closed in the ultraweak topology. -/
lemma isClosed_nonneg : IsClosed {x : σ(M, P) | 0 ≤ x} := by
  nontriviality σ(M, P)
  have : Nontrivial M := linearEquiv ℂ M P |>.symm.nontrivial
  set N := {x : σ(M, P) | 0 ≤ x}
  set S : Set σ(M, P) := ofUltraweak ⁻¹' (Metric.closedBall (0 : M) 1)
  set M_sa := {x : σ(M, P) | IsSelfAdjoint x}
  have h₁ : N ∩ S ⊆ (1 : σ(M, P)) +ᵥ M_sa ∩ S := by
    intro x ⟨hx_nonneg, hx_norm⟩
    refine ⟨x - 1, ⟨by aesop, ?_⟩, by simp⟩
    have := SpectrumRestricts.nnreal_iff_nnnorm (t := 1) hx_nonneg.isSelfAdjoint.ofUltraweak
      (by simpa [S] using! hx_norm) |>.mp <| SpectrumRestricts.nnreal_of_nonneg hx_nonneg
    simpa [norm_sub_rev, S] using NNReal.coe_le_coe.mpr this
  have h₂ : (1 : σ(M, P)) +ᵥ M_sa ∩ S ⊆ N := by
    rintro - ⟨x, ⟨hx_sa, hx⟩, rfl⟩
    simp only [vadd_eq_add, Set.mem_ofPred_eq, N]
    change 0 ≤ 1 + ofUltraweak x
    rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
      quasispectrumRestricts_iff_spectrumRestricts]
    refine ⟨by aesop, ?_⟩
    rw [SpectrumRestricts.nnreal_iff_nnnorm (t := 1 + 1)]
    · simpa using! norm_sub_le .. |>.trans <| by simpa [S] using hx
    · aesop
    · exact norm_add_le .. |>.trans <| by simpa [S] using hx
  have h₃ : IsClosed ((1 : σ(M, P)) +ᵥ M_sa ∩ S) :=
    isClosed_setOf_isSelfAdjoint.inter (isClosed_closedBall ℂ P (0 : M) 1) |>.vadd _
  refine Ultraweak.krein_smulian_of_submodule (Nonneg.nnrealSubmodule σ(M, P)) ?_
  convert h₃.inter (isClosed_closedBall ℂ P (0 : M) 1) using 1
  exact subset_antisymm (Set.subset_inter h₁ Set.inter_subset_right) (by gcongr; exact h₂)

set_option backward.isDefEq.respectTransparency false in
instance : OrderClosedTopology σ(M, P) where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

end Ultraweak
