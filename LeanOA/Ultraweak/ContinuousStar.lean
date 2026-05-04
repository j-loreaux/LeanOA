module

public import LeanOA.Ultraweak.OrderClosed
public import LeanOA.Mathlib.Analysis.RCLike.Extend
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open scoped NNReal Topology

namespace WeakDual

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/-- A linear map from the weak dual of a Banach space to itself is continuous if
it is continuous on the closed unit ball. -/
lemma continuous_of_continuousOn (f : WeakDual 𝕜 E →ₗ[𝕜] WeakDual 𝕜 E)
    (hf : ContinuousOn f (toStrongDual ⁻¹' Metric.closedBall 0 1)) : Continuous f := by
  refine continuous_of_continuous_eval fun x ↦ ?_
  let xf : Module.Dual 𝕜 (WeakDual 𝕜 E) :=
    WeakBilin.eval _ x |>.toLinearMap |>.comp f
  refine xf.continuous_of_isClosed_ker <| krein_smulian_of_submodule (xf.ker.restrictScalars ℝ≥0) ?_
  rw [Set.inter_comm]
  exact eval_continuous x |>.comp_continuousOn hf |>.preimage_isClosed_of_isClosed
    (isClosed_closedBall 0 1) isClosed_singleton

set_option backward.isDefEq.respectTransparency false in
/-- A *real* linear man from the weak dual of a Banach space to itself is continuous
if it is continuous on the closed unit ball. -/
lemma continuous_of_continuousOn_of_real (f : WeakDual 𝕜 E →ₗ[ℝ] WeakDual 𝕜 E)
    (hf : ContinuousOn f (toStrongDual ⁻¹' Metric.closedBall 0 1)) : Continuous f := by
  refine WeakBilin.continuous_of_continuous_eval_re _ fun x ↦ ?_
  let xf : Module.Dual ℝ (WeakDual 𝕜 E) :=
    Module.Dual.extendRCLikeₗ.symm.toLinearMap
      (WeakBilin.eval (topDualPairing 𝕜 E) x |>.toLinearMap) |>.comp f
  refine xf.continuous_of_isClosed_ker <| krein_smulian_of_submodule (xf.ker.restrictScalars ℝ≥0) ?_
  rw [Set.inter_comm]
  refine RCLike.continuous_re.comp_continuousOn (eval_continuous x |>.comp_continuousOn hf)
    |>.preimage_isClosed_of_isClosed (isClosed_closedBall 0 1) isClosed_singleton

end WeakDual

namespace Ultraweak

section generic

variable {𝕜 M P : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [Predual 𝕜 M P] [CompleteSpace P]

lemma continuous_of_continuousOn (f : σ(M, P)_𝕜 →ₗ[𝕜] σ(M, P)_𝕜)
    (hf : ContinuousOn f (ofUltraweak ⁻¹' Metric.closedBall 0 1)) :
    Continuous f := by
  -- transport the problem to the weak dual of `P`, then apply the result there.
  suffices Continuous ((weakDualCLE 𝕜 M P).toLinearEquiv.toLinearMap.comp <|
      f.comp (weakDualCLE 𝕜 M P).symm.toLinearEquiv.toLinearMap) from
    (weakDualCLE 𝕜 M P).symm.toHomeomorph.comp_continuous_iff'.mp <|
      (weakDualCLE 𝕜 M P).toHomeomorph.comp_continuous_iff.mp this
  refine WeakDual.continuous_of_continuousOn _ ?_
  refine map_continuous (weakDualCLE 𝕜 M P) |>.comp_continuousOn ?_
  refine hf.comp (map_continuous (weakDualCLE 𝕜 M P).symm).continuousOn fun x hx ↦ ?_
  rw [ofUltraweak_preimage_closedBall]
  simpa using hx

variable [Module ℝ M] [IsScalarTower ℝ 𝕜 M]
set_option backward.isDefEq.respectTransparency false in
lemma continuous_of_continuousOn_of_real (f : σ(M, P)_𝕜 →ₗ[ℝ] σ(M, P)_𝕜)
    (hf : ContinuousOn f (ofUltraweak ⁻¹' Metric.closedBall 0 1)) :
    Continuous f := by
  -- transport the problem to the weak dual of `P`, then apply the result there.
  suffices Continuous (((weakDualCLE 𝕜 M P).toLinearEquiv.toLinearMap.restrictScalars ℝ).comp <|
      f.comp <| (weakDualCLE 𝕜 M P).symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) from
    (weakDualCLE 𝕜 M P).symm.toHomeomorph.comp_continuous_iff'.mp <|
      (weakDualCLE 𝕜 M P).toHomeomorph.comp_continuous_iff.mp this
  refine WeakDual.continuous_of_continuousOn_of_real _ ?_
  refine map_continuous (weakDualCLE 𝕜 M P) |>.comp_continuousOn ?_
  refine hf.comp (map_continuous (weakDualCLE 𝕜 M P).symm).continuousOn fun x hx ↦ ?_
  rw [ofUltraweak_preimage_closedBall]
  simpa using hx

end generic

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [Predual ℂ M P] [CompleteSpace P]

set_option backward.isDefEq.respectTransparency false in
open Filter Complex in
open scoped Pointwise ComplexStarModule in
instance : ContinuousStar σ(M, P) where
  continuous_star := by
    -- It suffices to show that the `ℝ`-linear `realPart` map is continuous
    suffices Continuous ((selfAdjoint.submodule ℝ σ(M, P)).subtype.comp (realPart)) by
      convert (this.const_smul (2 : ℝ)).sub continuous_id using 2 with x
      -- `change` is necessary to see through the defeq between `selfAdjoint.submodule ℝ σ(M, P)
      -- and `selfAdjoint σ(M, P)`. To do this correctly, we would need to set up a linear
      -- equivalence between them.
      change star x = (2 : ℝ) • realPart x - x
      simp [realPart_apply_coe, smul_smul]
    /- Since this map is `ℝ`-linear, it suffices to show that it is
    continuous on the closed unit ball, for which it suffices to check that
    it is continuous within the closed unit ball at each `x`. -/
    refine Ultraweak.continuous_of_continuousOn_of_real _ ?_
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_def]
    intro x hx
    /- Because `realPart` is contractive, it stays within the closed unit ball
    along the `𝓝[closedUnitBall] x` filter. -/
    have h₁ : ∀ᶠ m in (𝓝[ofUltraweak ⁻¹' Metric.closedBall 0 1] x),
        (realPart m : σ(M, P)) ∈ ofUltraweak ⁻¹' Metric.closedBall 0 1 := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hm
      grw [← hm]
      simpa using realPart.norm_le (ofUltraweak m)
    /- Since the closed unit ball intersected with the selfadjoint elements
    is compact, it suffices to show that every selfadjoint `y` satisfying
    `mapClusterPt y (𝓝[ofUltraweak ⁻¹' Metric.closedBall 0 1] x) realPart`
    is precisely `realPart x`. -/
    refine Ultraweak.isCompact_closedBall ℂ P (0 : M) 1
      |>.inter_right Ultraweak.isClosed_setOf_isSelfAdjoint
      |>.tendsto_nhds_of_unique_mapClusterPt (by simpa using h₁)
      fun y ⟨_, (hy : IsSelfAdjoint y)⟩ hxy ↦ ?_
    /- Extract an ultrafilter `l` smaller than
    `𝓝[ofUltraweak ⁻¹' Metric.closedBall 0 1] x` such that `realPart` converges
    to `y` along `l`. Then `m ↦ m - realPart m` converges to `x - y` along
    `l`. -/
    obtain ⟨l, hl, hly⟩ := mapClusterPt_iff_ultrafilter.mp hxy
    have h₂ : Tendsto (fun m : σ(M, P) ↦ m - realPart m) l (𝓝 (x - y)) :=
      .sub (hl.trans nhdsWithin_le_nhds) hly
    /- Since `m ↦ m - realPart m` is always skewadjoint, and the skewadjoint
    element of `σ(M, P)` are closed, `x - y = I • z` for some selfadjoint `z`.
    Since `y` is also selfadjoint, we must have `y = realPart x`. -/
    obtain ⟨z, (hz : IsSelfAdjoint z), (hxyz : I • z = _)⟩ :=
      Ultraweak.isClosed_setOf_isSelfAdjoint.smul₀ I |>.mem_of_tendsto h₂ <|
        .of_forall fun m ↦ by
          nth_rewrite 1 [← realPart_add_I_smul_imaginaryPart m]
          simp
    simpa only [eq_comm (a := y), map_sub, AddSubgroupClass.coe_sub, hy.coe_realPart,
      realPart_I_smul, hz.imaginaryPart, neg_zero, ZeroMemClass.coe_zero, sub_eq_zero]
      using congr((ℜ $hxyz : σ(M, P))).symm

end Ultraweak
