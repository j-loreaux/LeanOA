module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Bornology.Real

@[expose] public section

/-! # The norm of `x + t` for large scalars `t`

If `x` is a selfadjoint element of a C⋆-algebra and `t ≥ ‖x‖` is real, then
`‖x + t‖ = t + max σ(x)` and `‖x - t‖ = t - min σ(x)`. In particular, `‖x + t‖ - t` and
`‖x - t‖ - t` are eventually constant as `t → ∞`, and so `x = 0` as soon as
`‖x + t‖ ≤ |t| + o(1)` as `|t| → ∞`. For a not necessarily selfadjoint `x` in a unital
C⋆-algebra, we deduce that `x = 0` as soon as `‖x + c‖ ≤ ‖c‖ + o(1)` as `‖c‖ → ∞` for `c : ℂ`.
-/

open scoped ComplexStarModule Topology
open Filter Complex Bornology

lemma tendsto_sqrt_add_sq_norm_sub_norm_cobounded {E : Type*} [SeminormedAddCommGroup E]
    (C : ℝ) : Tendsto (fun x : E ↦ √(C + ‖x‖ ^ 2) - ‖x‖) (cobounded E) (𝓝 0) := by
  /- Since `‖x‖ → ∞` as `x` tends to `cobounded E`, it suffices to consider `x : ℝ` with
  `x → ∞`. -/
  suffices Tendsto (fun x : ℝ ↦ √(C + x ^ 2) - x) atTop (𝓝 0) from
    this.comp tendsto_norm_cobounded_atTop
  /- For large `x`, `√(C + x ^ 2) - x = C / (√(C + x ^ 2) + x)`, and the denominator is at
  least `x`. -/
  have key : ∀ᶠ x in atTop, C / (√(C + x ^ 2) + x) = √(C + x ^ 2) - x := by
    filter_upwards [eventually_ge_atTop (|C| + 1)] with x hx
    have hx₀ : 0 < x := by linarith [abs_nonneg C]
    have hCx : 0 ≤ C + x ^ 2 := by nlinarith [neg_abs_le C]
    rw [div_eq_iff (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hx₀).ne']
    linear_combination -Real.sq_sqrt hCx
  exact .congr' key <| tendsto_const_nhds.div_atTop <|
    tendsto_id.nonneg_add_atTop fun _ ↦ Real.sqrt_nonneg _

namespace IsSelfAdjoint

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {x : A}

section Nontrivial

variable [Nontrivial A]

open ContinuousFunctionalCalculus in
/-- If `x` is selfadjoint and `‖x‖ ≤ t`, then `‖x + t‖ = t + max σ(x)`. -/
lemma norm_add_algebraMap_of_norm_le (hx : IsSelfAdjoint x) {t : ℝ}
    (ht : ‖x‖ ≤ t) : ‖x + algebraMap ℝ A t‖ = t + sSup (spectrum ℝ x) := by
  /- `x + t = cfc (· + t) x`, and `c + t ≥ 0` for every `c` in the spectrum, so the norm of
  `x + t` is the largest value of `c + t` on the spectrum. -/
  have h_cpct := isCompact_spectrum (R := ℝ) x
  have h_mem := h_cpct.sSup_mem (spectrum_nonempty x hx)
  have hσ {c : ℝ} (hc : c ∈ spectrum ℝ x) : ‖c + t‖ = c + t := by
    have := norm_apply_le_norm_cfc id x hc
    rw [cfc_id ℝ x, id, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, abs_of_nonneg]
    linarith [neg_abs_le c]
  have h := IsGreatest.norm_cfc (fun c : ℝ ↦ c + t) x
  rw [cfc_add_const t (fun c ↦ c) x, cfc_id' ℝ x] at h
  refine h.unique ⟨⟨_, h_mem, (hσ h_mem).trans (add_comm _ _)⟩, ?_⟩
  rintro - ⟨c, hc, rfl⟩
  linarith [hσ hc, le_csSup h_cpct.bddAbove hc]

/-- If `x` is selfadjoint and `‖x‖ ≤ t`, then `‖x - t‖ = t - min σ(x)`. -/
lemma norm_sub_algebraMap_of_norm_le (hx : IsSelfAdjoint x) {t : ℝ}
    (ht : ‖x‖ ≤ t) : ‖x - algebraMap ℝ A t‖ = t - sInf (spectrum ℝ x) := by
  have := hx.neg.norm_add_algebraMap_of_norm_le (t := t) (by rwa [norm_neg])
  rwa [← spectrum.neg_eq, Real.sSup_neg, ← sub_eq_add_neg, neg_add_eq_sub, norm_sub_rev] at this

/-- If `x` is selfadjoint, then `‖x + t‖ - |t|` is eventually equal to `max σ(x)` as `t → ∞`. -/
lemma norm_add_algebraMap_sub_abs_eventuallyEq_atTop (hx : IsSelfAdjoint x) :
    (fun t : ℝ ↦ ‖x + algebraMap ℝ A t‖ - |t|) =ᶠ[atTop] fun _ ↦ sSup (spectrum ℝ x) := by
  filter_upwards [eventually_ge_atTop ‖x‖] with t ht
  rw [hx.norm_add_algebraMap_of_norm_le ht, abs_of_nonneg ((norm_nonneg x).trans ht),
    add_sub_cancel_left]

/-- If `x` is selfadjoint, then `‖x + t‖ - |t|` is eventually equal to `-min σ(x)` as
`t → -∞`. -/
lemma norm_add_algebraMap_sub_abs_eventuallyEq_atBot (hx : IsSelfAdjoint x) :
    (fun t : ℝ ↦ ‖x + algebraMap ℝ A t‖ - |t|) =ᶠ[atBot] fun _ ↦ -sInf (spectrum ℝ x) := by
  filter_upwards [eventually_le_atBot (-‖x‖)] with t ht
  have := hx.norm_sub_algebraMap_of_norm_le (le_neg.mp ht)
  rw [map_neg, sub_neg_eq_add] at this
  rw [this, abs_of_nonpos (ht.trans (neg_nonpos.mpr (norm_nonneg x))), sub_sub_cancel_left]

end Nontrivial

/-- If `x` is selfadjoint and `‖x + t‖ ≤ |t| + o(1)` as `t → ∞`, then the spectrum of `x` is
nonpositive. -/
lemma spectrum_subset_Iic_of_norm_add_algebraMap_le_abs_add (hx : IsSelfAdjoint x)
    {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (h : ∀ᶠ t in atTop, ‖x + algebraMap ℝ A t‖ ≤ |t| + f t) : spectrum ℝ x ⊆ Set.Iic 0 := by
  nontriviality A
  /- `‖x + t‖ - |t|` is bounded above by `f t`, which tends to zero, and it is eventually equal to
  `max σ(x)`. -/
  have hsup : sSup (spectrum ℝ x) ≤ 0 := ge_of_tendsto hf <| by
    filter_upwards [h, hx.norm_add_algebraMap_sub_abs_eventuallyEq_atTop] with t ht ht'
    linarith
  have h_cpct := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) x
  exact fun c hc ↦ Set.mem_Iic.mpr <| (le_csSup h_cpct.bddAbove hc).trans hsup

/-- If `x` is selfadjoint and `‖x + t‖ ≤ |t| + o(1)` as `t → -∞`, then the spectrum of `x` is
nonnegative. -/
lemma spectrum_subset_Ici_of_norm_add_algebraMap_le_abs_add (hx : IsSelfAdjoint x)
    {f : ℝ → ℝ} (hf : Tendsto f atBot (𝓝 0))
    (h : ∀ᶠ t in atBot, ‖x + algebraMap ℝ A t‖ ≤ |t| + f t) : spectrum ℝ x ⊆ Set.Ici 0 := by
  nontriviality A
  /- `‖x + t‖ - |t|` is bounded above by `f t`, which tends to zero, and it is eventually equal to
  `-min σ(x)`. -/
  have hinf : 0 ≤ sInf (spectrum ℝ x) := neg_nonpos.mp <| ge_of_tendsto hf <| by
    filter_upwards [h, hx.norm_add_algebraMap_sub_abs_eventuallyEq_atBot] with t ht ht'
    linarith
  have h_cpct := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) x
  exact fun c hc ↦ Set.mem_Ici.mpr <| hinf.trans (csInf_le h_cpct.bddBelow hc)

/-- If `x` is selfadjoint and `‖x + t‖ ≤ |t| + o(1)` as `|t| → ∞`, then `x = 0`. -/
lemma eq_zero_of_norm_add_algebraMap_le_abs_add (hx : IsSelfAdjoint x)
    {f : ℝ → ℝ} (hf : Tendsto f (cobounded ℝ) (𝓝 0))
    (h : ∀ᶠ t in cobounded ℝ, ‖x + algebraMap ℝ A t‖ ≤ |t| + f t) : x = 0 := by
  have hle := hx.spectrum_subset_Iic_of_norm_add_algebraMap_le_abs_add
    (hf.mono_left IsOrderBornology.atTop_le_cobounded)
    (h.filter_mono IsOrderBornology.atTop_le_cobounded)
  have hge := hx.spectrum_subset_Ici_of_norm_add_algebraMap_le_abs_add
    (hf.mono_left IsOrderBornology.atBot_le_cobounded)
    (h.filter_mono IsOrderBornology.atBot_le_cobounded)
  exact CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) x
    (Set.Icc_self (0 : ℝ) ▸ Set.subset_inter hge hle) hx

end IsSelfAdjoint

/-- An element `x` of a unital C⋆-algebra such that `‖x + c‖ ≤ ‖c‖ + o(1)` as `‖c‖ → ∞` for
`c : ℂ` is zero. -/
lemma eq_zero_of_norm_add_algebraMap_le_norm_add {A : Type*} [CStarAlgebra A] {x : A}
    {f : ℂ → ℝ} (hf : Tendsto f (cobounded ℂ) (𝓝 0))
    (h : ∀ᶠ c in cobounded ℂ, ‖x + algebraMap ℂ A c‖ ≤ ‖c‖ + f c) : x = 0 := by
  /- The real and imaginary parts of `x` satisfy the hypotheses of
  `IsSelfAdjoint.eq_zero_of_norm_add_algebraMap_le_abs_add`, using `c = t` and `c = I * t`
  respectively. -/
  have h_re : Tendsto (fun t : ℝ ↦ (t : ℂ)) (cobounded ℝ) (cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp <|
      (tendsto_norm_cobounded_atTop (E := ℝ)).congr fun t ↦ by simp
  have h_im : Tendsto (fun t : ℝ ↦ I * t) (cobounded ℝ) (cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp <|
      (tendsto_norm_cobounded_atTop (E := ℝ)).congr fun t ↦ by simp
  have hre : (ℜ x : A) = 0 := by
    refine (ℜ x).2.eq_zero_of_norm_add_algebraMap_le_abs_add (hf.comp h_re) ?_
    filter_upwards [h_re.eventually h] with t ht
    simpa [Algebra.algebraMap_eq_smul_one, (IsSelfAdjoint.one (R := A)).coe_realPart] using
      (realPart.norm_le (x + algebraMap ℂ A t)).trans ht
  have him : (ℑ x : A) = 0 := by
    refine (ℑ x).2.eq_zero_of_norm_add_algebraMap_le_abs_add (hf.comp h_im) ?_
    filter_upwards [h_im.eventually h] with t ht
    simpa [Algebra.algebraMap_eq_smul_one, mul_smul, imaginaryPart_I_smul,
      (IsSelfAdjoint.one (R := A)).coe_realPart] using
      (imaginaryPart.norm_le (x + algebraMap ℂ A (I * t))).trans ht
  rw [← realPart_add_I_smul_imaginaryPart x, hre, him, smul_zero, add_zero]
