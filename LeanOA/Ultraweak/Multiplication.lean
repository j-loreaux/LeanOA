module

public import LeanOA.CStarAlgebra.OffDiagonal
public import LeanOA.Ultraweak.Corner
public import LeanOA.Ultraweak.Dual
public import LeanOA.Ultraweak.FiniteSpectrum
import Mathlib.Analysis.Normed.Module.Ray

@[expose] public section

/-! # Multiplication is separately ultraweakly continuous

This file shows that left and right multiplication by a fixed element are ultraweakly continuous
on a W⋆-algebra (Sakai 1.7.6–1.7.8). We follow the treatment in arXiv:2009.05825, §5.3.

For a projection `p` with complement `q = 1 - p`, we first show that the off-diagonal corner
`p * M * q` meets the closed unit ball in an ultraweakly closed set, using the norm estimates
in `LeanOA.CStarAlgebra.OffDiagonal`. It follows that `p * M` is ultraweakly closed, and hence
that left multiplication by `p`, being a bounded idempotent with closed range and kernel, is
ultraweakly continuous. Since the span of the projections is norm dense in `M`, left
multiplication by any element is ultraweakly continuous; right multiplication follows by taking
adjoints.

## Main declarations

+ `Ultraweak.instSeparatelyContinuousMul`: multiplication on `σ(M, P)` is separately continuous,
  so that `σ(M, P)` is a semitopological ring (`Ultraweak.instIsSemitopologicalRing`).
-/

open scoped Ultraweak NNReal Pointwise Topology StarRing
open Metric Filter Set

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace Ultraweak

section Projection

variable {p q : σ(M, P)} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0)
  (hpq₁ : p + q = 1)
include hp hq hpq hpq₁

attribute [local grind =>] IsIdempotentElem.mul_mul_self IsIdempotentElem.mul_self_mul
  IsIdempotentElem.eq

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
/-- The intersection of the off-diagonal corner `p * M * q` with the closed unit ball is
ultraweakly closed. -/
lemma closure_image_mul_mul_subset :
    closure ((fun y ↦ p * y * q) '' (ofUltraweak ⁻¹' closedBall (0 : M) 1)) ⊆
      (fun y ↦ p * y * q) '' (ofUltraweak ⁻¹' closedBall (0 : M) 1) := by
  intro x hx
  lift p to M using trivial
  lift q to M using trivial
  lift x to M using trivial
  simp only [isStarProjection_toUltraweak] at hp hq
  replace hpq : p ⋆⟂ q := (isStarOrtho_iff_mul_eq_zero hp.isSelfAdjoint hq.isSelfAdjoint).mpr <| by
    simpa using congr(ofUltraweak $hpq)
  replace hpq₁ : p + q = 1 := by simpa using congr(ofUltraweak $hpq₁)
  /- Any bound on `‖p * y * q + b‖` for `y` in the closed unit ball passes to `x + b`, since the
  closed balls are ultraweakly closed. -/
  have key (b : M) (r : ℝ) (h : ∀ y : M, ‖y‖ ≤ 1 → ‖p * y * q + b‖ ≤ r) : ‖x + b‖ ≤ r := by
    have := map_mem_closure (f := fun z ↦ z + toUltraweak ℂ P b) (by fun_prop)
      hx (t := ofUltraweak ⁻¹' closedBall (0 : M) r) <| by
        rintro - ⟨y, hy, rfl⟩
        simpa using h (ofUltraweak y) (by simpa using hy)
    simpa using (isClosed_closedBall ℂ P (0 : M) r).closure_subset this
  /- The diagonal corners of `x` vanish. -/
  have hpxp : p * x * p = 0 :=
    hp.mul_mul_eq_zero_of_norm_add_smul_le 1 fun c ↦
      key (c • p) _ fun y hy ↦ hp.norm_mul_mul_add_smul_le hq hpq hy c
  have hqxq : q * x * q = 0 :=
    hq.mul_mul_eq_zero_of_norm_add_smul_le 1 fun c ↦
      key (c • q) _ fun y hy ↦ hp.norm_mul_mul_add_smul_le' hq hpq hy c
  have hx_dec : x = p * x * q + q * x * p := by
    calc x = (p + q) * x * (p + q) := by rw [hpq₁, one_mul, mul_one]
      _ = _ := by
        simp only [add_mul, mul_add, hpxp, hqxq, zero_add, add_zero]
        exact add_comm _ _
  /- The lower left corner of `x` vanishes. -/
  have hqxp : q * x * p = 0 := by
    /- Otherwise, adding the unit vector `u` in the direction of `q * x * p` gives
    `‖q * x * p‖ + 1 = ‖q * (x + u) * p‖ ≤ ‖x + u‖ ≤ 1`. -/
    by_contra! hqxp
    set u := ‖q * x * p‖⁻¹ • (q * x * p)
    have hu : q * u * p = u := by grind [mul_assoc, mul_smul_comm, smul_mul_assoc]
    have hu₁ : ‖u‖ = 1 := by simp [u, norm_smul, hqxp]
    suffices ‖q * x * p‖ + 1 ≤ 1 by simpa [hu₁, hqxp]
    calc
      ‖q * x * p‖ + 1 = ‖q * (x + u) * p‖ := by
        rw [mul_add, add_mul, hu, SameRay.norm_add, hu₁]
        exact (.sameRay_nonneg_smul_right _ (by positivity))
      _ ≤ ‖x + u‖ := by grw [norm_mul₃_le, hq.norm_le, hp.norm_le]; simp
      _ ≤ 1 := by simpa [hu₁] using key u _ (fun y hy ↦ hp.norm_mul_mul_add_le_max hq hpq hy hu)
  /- Hence `x = p * x * q`, and `x` lies in the closed unit ball since it is closed. -/
  have hx_ball : toUltraweak ℂ P x ∈ ofUltraweak ⁻¹' closedBall (0 : M) 1 := by
    refine (isClosed_closedBall ℂ P (0 : M) 1).closure_subset_iff.mpr ?_ hx
    rintro - ⟨y, hy, rfl⟩
    simp only [mem_preimage, mem_closedBall, dist_zero_right, ofUltraweak_mul,
      ofUltraweak_toUltraweak] at hy ⊢
    grw [norm_mul₃_le, hy]
    bound
  refine ⟨_, hx_ball, ?_⟩
  simpa [hqxp] using congr(toUltraweak ℂ P $hx_dec.symm)

/-- The intersection of `p * M` with the closed unit ball is ultraweakly compact. -/
lemma isCompact_image_mul_left :
    IsCompact ((p * ·) '' (ofUltraweak ⁻¹' closedBall (0 : M) 1)) := by
  set S : Set σ(M, P) := ofUltraweak ⁻¹' closedBall (0 : M) 1
  have hS : IsCompact S := isCompact_closedBall ℂ P (0 : M) 1
  have hpp := hp.isIdempotentElem.eq
  /- Multiplying an element of `S` by projections on either side stays in `S`. -/
  have h_norm (a y b : σ(M, P)) (ha : IsStarProjection a) (hb : IsStarProjection b)
      (hy : y ∈ S) : a * y * b ∈ S := by
    simp only [S, mem_preimage, mem_closedBall, dist_zero_right, ofUltraweak_mul] at hy ⊢
    grw [norm_mul₃_le, ha.ofUltraweak.norm_le, hy, hb.ofUltraweak.norm_le]
    simp
  have h_off : IsCompact ((fun y ↦ p * y * q) '' S) :=
    hS.of_isClosed_subset
      (closure_subset_iff_isClosed.mp (closure_image_mul_mul_subset hp hq hpq hpq₁))
      (by rintro - ⟨y, hy, rfl⟩; exact h_norm _ _ _ hp hq hy)
  have h_diag : IsCompact (range (p * · * p) ∩ S) := by
    refine hS.inter_left ?_
    rw [← hp.coe_cornerSubmodule_eq_range_mul_mul (R := ℂ)]
    exact hp.isClosed_cornerSubmodule_of_ultraweak
  /- `p * S = (p * S * p + p * S * q) ∩ S`. -/
  convert (h_diag.add h_off).inter_right (isClosed_closedBall ℂ P (0 : M) 1) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨p * y * p, ⟨⟨y, rfl⟩,
      h_norm _ _ _ hp hp hy⟩, p * y * q, ⟨y, hy, rfl⟩, ?_⟩, ?_⟩
    · change p * y * p + p * y * q = p * y
      rw [← mul_add, hpq₁, mul_one]
    · exact (by simpa using h_norm p y 1 hp (.one _) hy : p * y ∈ S)
  · rintro ⟨⟨-, ⟨⟨z, rfl⟩, -⟩, -, ⟨y, -, rfl⟩, rfl⟩, hx⟩
    refine ⟨_, hx, ?_⟩
    simp [mul_add, ← mul_assoc, hpp]

end Projection

section LeftMulProjection

variable {p : σ(M, P)} (hp : IsStarProjection p)
include hp

/-- For a projection `p`, the right ideal `p * M` is ultraweakly closed. -/
lemma isClosed_range_mulLeft :
    IsClosed (LinearMap.range (LinearMap.mulLeft ℂ p) : Set σ(M, P)) := by
  have hpq : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self]
  refine Ultraweak.krein_smulian_of_submodule
    ((LinearMap.range (LinearMap.mulLeft ℂ p)).restrictScalars ℝ≥0) ?_
  convert (isCompact_image_mul_left hp hp.one_sub hpq (add_sub_cancel p 1)).isClosed using 1
  ext x
  simp only [Submodule.coe_restrictScalars, LinearMap.coe_range, LinearMap.mulLeft_apply,
    mem_inter_iff, mem_range, mem_image]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨p * y, hy, by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    simp only [mem_preimage, mem_closedBall, dist_zero_right, ofUltraweak_mul] at hy ⊢
    exact (norm_mul_le _ _).trans <| by
      simpa using mul_le_mul hp.ofUltraweak.norm_le hy (norm_nonneg _) zero_le_one

/-- Left multiplication by a projection is ultraweakly continuous. -/
lemma continuous_mul_left_of_isStarProjection : Continuous (fun x : σ(M, P) ↦ p * x) := by
  have hpp := hp.isIdempotentElem.eq
  refine continuous_of_isIdempotentElem (LinearMap.mulLeft ℂ p) ?_ 1 (fun x ↦ ?_)
    (isClosed_range_mulLeft hp) ?_
  · ext x
    simp [← mul_assoc, hpp]
  · change ‖ofUltraweak p * ofUltraweak x‖ ≤ 1 * ‖ofUltraweak x‖
    exact (norm_mul_le _ _).trans <|
      mul_le_mul_of_nonneg_right hp.ofUltraweak.norm_le (norm_nonneg (ofUltraweak x))
  /- The kernel of left multiplication by `p` is the range of left multiplication by `1 - p`. -/
  · convert isClosed_range_mulLeft hp.one_sub using 1
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mem_range]
    constructor
    · exact fun h ↦ ⟨x, by rw [sub_mul, one_mul, h, sub_zero]⟩
    · rintro ⟨y, rfl⟩
      rw [← mul_assoc, mul_sub, mul_one, hpp, sub_self, zero_mul]

end LeftMulProjection

/-- Left multiplication is ultraweakly continuous. -/
private theorem continuous_mul_left (a : σ(M, P)) : Continuous (fun x : σ(M, P) ↦ a * x) := by
  /- For each `ρ : P`, let `Φ ρ : M →L[ℂ] StrongDual ℂ M` send `b` to `x ↦ equivDual (b * x) ρ`.
  Then the set `T` of those `b` for which left multiplication by `b` is ultraweakly continuous is
  the intersection of the preimages under the maps `Φ ρ` of the (norm closed) range of
  `Predual.toDual`. Hence `T` is a norm closed subspace which, by the above, contains the
  projections. Since the span of the projections is dense, `T` is everything. -/
  let Φ (ρ : P) : M →L[ℂ] StrongDual ℂ M :=
    (ContinuousLinearMap.compL ℂ M M ℂ (Predual.toDual ℂ M P ρ)).comp
      (ContinuousLinearMap.mul ℂ M)
  let T : Submodule ℂ M :=
    ⨅ ρ, (LinearMap.range (Predual.toDual ℂ M P).toLinearMap).comap (Φ ρ).toLinearMap
  have hT_iff (b : M) : b ∈ T ↔ Continuous (fun x : σ(M, P) ↦ toUltraweak ℂ P b * x) := by
    simp only [T, Submodule.mem_iInf, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    refine ⟨fun h ↦ continuous_of_continuous_eval fun ρ ↦ ?_, fun h ρ ↦ ?_⟩
    · have := (continuous_iff_mem_range (P := P) (Φ ρ b)).mpr (by simpa using h ρ)
      simpa [Φ] using this
    · have := (eval_continuous (𝕜 := ℂ) (M := M) ρ).comp h
      simpa using (continuous_iff_mem_range (P := P) (Φ ρ b)).mp
        (by simpa [Φ, Function.comp_def] using this)
  have hT_closed : IsClosed (T : Set M) := by
    simp only [T, Submodule.coe_iInf, Submodule.comap_coe, LinearMap.coe_range]
    exact isClosed_iInter fun ρ ↦ Predual.isClosed_range_toDual.preimage (Φ ρ).continuous
  have hT_proj : Submodule.span ℂ {p : M | IsStarProjection p} ≤ T :=
    Submodule.span_le.mpr fun p hp ↦ (hT_iff p).mpr <|
      continuous_mul_left_of_isStarProjection hp.toUltraweak
  have : CStarAlgebra.FiniteSpectrum M := CStarAlgebra.finiteSpectrum_of_predual (P := P)
  have := Submodule.topologicalClosure_minimal _ hT_proj hT_closed
  rw [CStarAlgebra.FiniteSpectrum.topologicalClosure_span_complex_isStarProjection] at this
  exact (hT_iff (ofUltraweak a)).mp (this trivial)

/-- **Sakai 1.7.8**: multiplication on `σ(M, P)` is separately ultraweakly continuous. -/
instance instSeparatelyContinuousMul : SeparatelyContinuousMul σ(M, P) where
  continuous_const_mul := continuous_mul_left _
  continuous_mul_const {a} := by
    have := (continuous_star.comp (continuous_mul_left (star a))).comp continuous_star
    simpa [Function.comp_def, star_mul] using this

/-- `σ(M, P)` is a semitopological ring. -/
instance instIsSemitopologicalRing : IsSemitopologicalRing σ(M, P) where

end Ultraweak
