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
  /- Each `q ∈ d` satisfies `q ≤ e ≤ 1`, so `0 ≤ q * (1 - e) * q ≤ q * (1 - q) * q = 0`, whence
  `(1 - e) * q = 0`, i.e., `e * q = q`. -/
  have h₂ (q : d) : e * q = q := by
    have hq := hdp q q.2
    have h₀ : 0 ≤ 1 - e := sub_nonneg.mpr <| he.2 fun q hq ↦ (hdp q hq).le_one
    have : q * (1 - e) * q = 0 := le_antisymm
      (by simpa [mul_sub, sub_mul, hq.isIdempotentElem.eq] using
        hq.isSelfAdjoint.conjugate_le_conjugate (sub_le_sub_left (he.1 q.2) 1))
      (hq.isSelfAdjoint.conjugate_nonneg h₀)
    simpa [sub_mul, sub_eq_zero, hq.isSelfAdjoint.star_eq, eq_comm] using
      mul_star_eq_zero_of_mul_mul_star_eq_zero h₀ (c := (q : M)) (by rwa [hq.isSelfAdjoint.star_eq])
  /- Since multiplication is separately ultraweakly continuous, `e * q = q` tends to `e * e`, but
  it also tends to `e`. -/
  have h₃ := ((continuous_const_mul (toUltraweak ℂ P e)).tendsto _).comp h₁
  simp only [Function.comp_def, ← toUltraweak_mul, h₂] at h₃
  exact ⟨toUltraweak_injective (tendsto_nhds_unique h₃ h₁), hsa⟩

end Ultraweak
