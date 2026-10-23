module

public import LeanOA.Ultraweak.Multiplication
public import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Order.ScottContinuity
public import Mathlib.Analysis.CStarAlgebra.Projection

@[expose] public section

/-! # Normal positive functionals

A positive linear functional `φ` on a W⋆-algebra `M` is *normal* if it preserves suprema of
directed sets, i.e., if it is `ScottContinuous`. This file shows that ultraweakly continuous
positive functionals are normal, and that the supremum of a directed set of projections is again
a projection.
-/

open scoped Ultraweak ComplexOrder Topology
open Filter Set

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace Ultraweak

variable (P) in
/-- Along a nonempty directed set `d` with supremum `a`, the inclusion of `d` into `σ(M, P)`
tends to `a`. -/
lemma tendsto_toUltraweak_of_isLUB {d : Set M} {a : M} (ha : IsLUB d a) :
    Tendsto (fun x : d ↦ toUltraweak ℂ P (x : M)) atTop (𝓝 (toUltraweak ℂ P a)) := by
  refine tendsto_atTop_isLUB (monotone_toUltraweak.comp (Subtype.mono_coe _)) ?_
  rw [Set.range_comp', Subtype.range_coe]
  exact (ofUltraweakOrderIso (M := M) (P := P)).symm.isLUB_image.mpr ha

include P in
/-- An ultraweakly continuous positive linear functional is normal, i.e., it preserves suprema
of directed sets. -/
theorem scottContinuous_of_continuous (φ : M →ₚ[ℂ] ℂ)
    (hφ : Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x)) : ScottContinuous φ := by
  intro d hne hd a ha
  have : Nonempty d := hne.to_subtype
  have : IsDirectedOrder d := ⟨hd.directed_val⟩
  have h : Tendsto (fun x : d ↦ φ (x : M)) atTop (𝓝 (φ a)) :=
    (hφ.tendsto _).comp (tendsto_toUltraweak_of_isLUB P ha)
  have := isLUB_of_tendsto_atTop ((OrderHomClass.mono φ).comp (Subtype.mono_coe (· ∈ d))) h
  rwa [Set.range_comp, Subtype.range_coe] at this

include P in
/-- In a W⋆-algebra, the supremum of a nonempty directed set of projections is a projection. -/
theorem isStarProjection_of_isLUB {d : Set M} (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d)
    (hdp : ∀ q ∈ d, IsStarProjection q) {e : M} (he : IsLUB d e) : IsStarProjection e := by
  have : Nonempty d := hne.to_subtype
  have : IsDirectedOrder d := ⟨hd.directed_val⟩
  have h₁ := tendsto_toUltraweak_of_isLUB P he
  have hsa : IsSelfAdjoint e :=
    isClosed_setOf_isSelfAdjoint.mem_of_tendsto h₁ (.of_forall fun q ↦ (hdp q q.2).isSelfAdjoint)
  have he₁ : e ≤ 1 := he.2 fun q hq ↦ (hdp q hq).le_one
  /- The elements `e - q` for `q ∈ d` are nonnegative contractions tending ultraweakly to `0`;
  hence so are their squares, since `(e - q) * (e - q) ≤ e - q`. -/
  have hx (q : d) : 0 ≤ e - q ∧ ‖e - q‖ ≤ 1 := by
    have h₀ : 0 ≤ e - q := sub_nonneg.mpr (he.1 q.2)
    refine ⟨h₀, (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one h₀).mpr ?_⟩
    simpa using (sub_le_self e (hdp q q.2).nonneg).trans he₁
  have h₂ : Tendsto (fun q : d ↦ toUltraweak ℂ P ((e - q) * (e - q))) atTop (𝓝 0) := by
    refine tendsto_of_forall_posCLM_of_eventually (r := 1) (.of_forall fun q ↦ ?_) fun φ ↦ ?_
    · simp only [ofUltraweak_toUltraweak]
      exact (norm_mul_le _ _).trans <| by nlinarith [norm_nonneg (e - q), (hx q).2]
    have hφ : Tendsto (fun q : d ↦ φ (toUltraweak ℂ P (e - q))) atTop (𝓝 0) := by
      have := ((map_continuous φ).tendsto _).comp
        ((tendsto_const_nhds (x := toUltraweak ℂ P e)).sub h₁)
      simpa only [Function.comp_def, sub_self, map_zero, ← toUltraweak_sub] using this
    rw [map_zero]
    refine squeeze_zero_norm (fun q ↦ ?_) (tendsto_zero_iff_norm_tendsto_zero.mp hφ)
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (OrderHomClass.mono φ <| toUltraweak_le.mpr <|
        CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one (hx q).1 (hx q).2)
      (map_nonneg φ <| toUltraweak_nonneg.mpr (hx q).1.isSelfAdjoint.mul_self_nonneg)
  /- On the other hand, `(e - q) * (e - q) = e * e - e * q - q * e + q` tends to `e - e * e`,
  since multiplication is separately ultraweakly continuous. Hence `e * e = e`. -/
  have hL := ((continuous_const_mul (toUltraweak ℂ P e)).tendsto _).comp h₁
  have hR := ((continuous_mul_const (toUltraweak ℂ P e)).tendsto _).comp h₁
  have h₃ := ((tendsto_const_nhds (x := toUltraweak ℂ P (e * e))).sub hL |>.sub hR).add h₁
  have h₄ : Tendsto (fun q : d ↦ toUltraweak ℂ P ((e - q) * (e - q))) atTop
      (𝓝 (toUltraweak ℂ P (e - e * e))) := by
    refine h₃.congr' (.of_forall fun q ↦ ?_) |>.trans (le_of_eq ?_)
    · simp [sub_mul, mul_sub, (hdp q q.2).isIdempotentElem.eq]
      abel
    · congr 1
      simp only [← toUltraweak_mul, ← toUltraweak_sub, ← toUltraweak_add]
      congr 1
      abel
  have := (toUltraweak_eq_zero (x := e - e * e)).mp (tendsto_nhds_unique h₄ h₂)
  exact ⟨(sub_eq_zero.mp this).symm, hsa⟩

end Ultraweak
