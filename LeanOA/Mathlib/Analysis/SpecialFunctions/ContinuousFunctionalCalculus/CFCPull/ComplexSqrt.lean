/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import LeanOA.Mathlib.Tactic.CFCPull

/-!  # `CFC.sqrt` via the complex functional calculus -/

public section

open scoped NNReal

namespace Complex

/-- `Complex.sqrt` is continuous on the closed right half-plane. -/
lemma continuousOn_sqrt_setOf_re_nonneg : ContinuousOn sqrt {z | 0 ≤ z.re} :=
  fun _z hz ↦ (continuousAt_sqrt (.inl hz)).continuousWithinAt

end Complex

section NonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] [NonnegSpectrumClass ℝ A] {a : A}

/-- The `ℂ`-quasispectrum of a nonnegative element lies in the closed right half-plane, where
`Complex.sqrt` is continuous. -/
@[fun_prop]
lemma Complex.continuousOn_sqrt_quasispectrum (ha : 0 ≤ a) :
    ContinuousOn Complex.sqrt (quasispectrum ℂ a) := by
  refine Complex.continuousOn_sqrt_setOf_re_nonneg.mono ?_
  rw [← ha.isSelfAdjoint.quasispectrumRestricts.algebraMap_image]
  rintro - ⟨x, hx, rfl⟩
  simpa using quasispectrum_nonneg_of_nonneg a ha x hx

variable [IsSemitopologicalRing A] [T2Space A]

/-- `CFC.sqrt` is the non-unital calculus over `ℂ` applied to `Complex.sqrt`. This is not
tagged `@[cfc_pull]` because it could generate side goals involving continuity of `Complex.sqrt`,
which are not easily discharged by `fun_prop`. -/
lemma CFC.sqrt_eq_cfcₙ_complex_sqrt (ha : 0 ≤ a) :
    CFC.sqrt a = cfcₙ (fun x : ℂ ↦ x.sqrt) a := by
  cfc_pull ℂ a
  refine cfcₙ_congr ?_
  rw [← (ha.isSelfAdjoint.quasispectrumRestricts.comp rfl (.nnreal_of_nonneg ha)).algebraMap_image]
  rintro - ⟨x, hx, rfl⟩
  rw [IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ]
  aesop (add simp [Complex.sqrt_of_nonneg])

end NonUnital

section Unital

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ A IsStarNormal]
  [NonnegSpectrumClass ℝ A] {a : A}

/-- The `ℂ`-spectrum of a nonnegative element lies in the closed right half-plane, where
`Complex.sqrt` is continuous. -/
@[fun_prop]
lemma Complex.continuousOn_sqrt_spectrum (ha : 0 ≤ a) :
    ContinuousOn Complex.sqrt (spectrum ℂ a) := by
  refine Complex.continuousOn_sqrt_setOf_re_nonneg.mono ?_
  rw [← ha.isSelfAdjoint.spectrumRestricts.algebraMap_image]
  rintro - ⟨x, hx, rfl⟩
  simpa using spectrum_nonneg_of_nonneg ha hx

variable [IsSemitopologicalRing A] [T2Space A]

/-- `CFC.sqrt` is the unital calculus over `ℂ` applied to `Complex.sqrt`. This is not
tagged `@[cfc_pull]` because it could generate side goals involving continuity of `Complex.sqrt`,
which are not easily discharged by `fun_prop`. -/
lemma CFC.sqrt_eq_cfc_complex_sqrt (ha : 0 ≤ a) :
    CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt) a := by
  cfc_pull -unital [CFC.sqrt_eq_cfcₙ_complex_sqrt] ℂ a

end Unital
