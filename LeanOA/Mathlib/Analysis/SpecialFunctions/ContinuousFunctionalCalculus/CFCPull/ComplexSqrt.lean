/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import LeanOA.Mathlib.Tactic.CFCPull

/-!
# `CFC.sqrt` via the complex functional calculus

`CFC.sqrt` is defined by the non-unital continuous functional calculus over `ℝ≥0`. On a
nonnegative element it agrees with the calculus applied to `Complex.sqrt`, which is what one
wants when the surrounding computation is taking place over `ℂ`.

## Main results

* `Complex.continuousOn_sqrt_setOf_re_nonneg`: `Complex.sqrt` is continuous on the closed right
  half-plane.
* `Complex.continuousOn_sqrt_quasispectrum`, `Complex.continuousOn_sqrt_spectrum`:
  `Complex.sqrt` is continuous on the (quasi)spectrum of a nonnegative element, which is what
  makes the calculus applicable to it in the first place.
* `CFC.sqrt_eq_cfcₙ_complex_sqrt`, `CFC.sqrt_eq_cfc_complex_sqrt`: `CFC.sqrt a = cfcₙ
  Complex.sqrt a` and `CFC.sqrt a = cfc Complex.sqrt a` for `0 ≤ a`.

## Implementation notes

Neither of the last two is tagged `@[cfc_pull]`, unlike its real counterpart
`CFC.sqrt_eq_real_sqrt`. `Complex.sqrt` is continuous only away from the negative reals, so a
`cfc_pull` that met a square root would raise a `ContinuousOn Complex.sqrt ..` goal that it can
discharge only when the element is *known* to be nonnegative — the two lemmas above are what does
it, but they need `0 ≤ a` in hand. Name the lemma where it is wanted instead:

```lean
example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_pull [CFC.sqrt_eq_cfc_complex_sqrt] ℂ a
```
-/

public section

open scoped NNReal

namespace Complex

/-- `Complex.sqrt` is continuous on the closed right half-plane. This is not comparable with
`Complex.continuousOn_sqrt`: `slitPlane` omits `0` but includes the points with negative real
part and nonzero imaginary part. -/
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

/-- `CFC.sqrt` is the non-unital calculus over `ℂ` applied to `Complex.sqrt`. See the module
docstring for why this is not tagged `@[cfc_pull]`. -/
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

/-- `CFC.sqrt` is the unital calculus over `ℂ` applied to `Complex.sqrt`. See the module
docstring for why this is not tagged `@[cfc_pull]`. -/
lemma CFC.sqrt_eq_cfc_complex_sqrt (ha : 0 ≤ a) :
    CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt) a := by
  -- the pull runs in the non-unital calculus, which is the one the lemma named is about;
  -- `cfcₙ_eq_cfc` then takes the right-hand side there too, and the two sides meet
  cfc_pull -unital [CFC.sqrt_eq_cfcₙ_complex_sqrt] ℂ a

end Unital
