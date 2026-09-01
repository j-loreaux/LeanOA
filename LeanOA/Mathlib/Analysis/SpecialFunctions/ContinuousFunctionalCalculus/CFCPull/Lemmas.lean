/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Lemmas needed by the `cfc_pull` tactic

`cfc_pull` (see `LeanOA/Mathlib/Tactic/CFCPull/Spec.md`) rewrites an expression built out of
`cfc`/`cfcₙ` applications into a single one. To do that it needs, for every operation that is
*secretly* an application of the calculus, a lemma exhibiting it as such. Mathlib already has
most of them; this file collects the ones it was missing, so that the tactic and its supporting
material stay in one place instead of being sprinkled over the library.

## Main results

* `CFC.sqrt_def`, `CFC.abs_def`, `CFC.log_def`: `CFC.sqrt`, `CFC.abs` and `CFC.log` unfolded to
  the calculus applied to `NNReal.sqrt`, `NNReal.sqrt` (at `star a * a`) and `Real.log`. All
  three are `rfl`.
* `cfcHom_eq_cfc_extend_zero`, `cfcₙHom_eq_cfcₙ_extend_zero`: the `g := 0` specialisations of
  `cfcHom_eq_cfc_extend` and `cfcₙHom_eq_cfcₙ_extend`, which are what the tactic uses to turn a
  bare `cfcHom`/`cfcₙHom` application into a `cfc`/`cfcₙ` one.
* `CFC.quasispectrum_nonpos_of_nonpos`, `CFC.nonpos_of_mem_quasispectrum`: the nonpositive
  counterparts of `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`, together with a
  `grind_pattern` for the latter.

Everything here belongs in the file that defines the operation it is about; it lives here only
so that `cfc_pull` can be reviewed and landed without touching those files. See
`LeanOA/Mathlib/Tactic/CFCPull/Design.md` §7.
-/

@[expose] public section

open scoped NNReal
open Topology ContinuousMap ContinuousMapZero

section Extend

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]

section Unital

variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- The `g := 0` case of `cfcHom_eq_cfc_extend`. -/
lemma cfcHom_eq_cfc_extend_zero {a : A} (ha : p a) (f : C(spectrum R a, R)) :
    cfcHom ha f = cfc (Function.extend Subtype.val f 0) a :=
  cfcHom_eq_cfc_extend 0 ha f

end Unital

section NonUnital

variable [Nontrivial R] [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R A p]

/-- The `g := 0` case of `cfcₙHom_eq_cfcₙ_extend`. -/
lemma cfcₙHom_eq_cfcₙ_extend_zero {a : A} (ha : p a) (f : C(quasispectrum R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f 0) a :=
  cfcₙHom_eq_cfcₙ_extend 0 ha f

end NonUnital

end Extend

namespace CFC

section Quasispectrum

-- TODO: these two results and the `grind` pattern should move next to
-- `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`.

lemma quasispectrum_nonpos_of_nonpos {𝕜 A : Type*} [CommRing 𝕜]
    [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [NonUnitalRing A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) (ha : a ≤ 0) :
    ∀ x ∈ quasispectrum 𝕜 a, x ≤ 0 := by
  have := quasispectrum_nonneg_of_nonneg (𝕜 := 𝕜) (-a) (by simpa using ha)
  simpa [Unitization.quasispectrum_eq_spectrum_inr 𝕜, ← spectrum.neg_eq]

lemma nonpos_of_mem_quasispectrum {𝕜 A : Type*} [CommRing 𝕜]
    [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [NonUnitalRing A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {a : A} (ha : a ≤ 0) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : x ≤ 0 := quasispectrum_nonpos_of_nonpos a ha x hx

grind_pattern nonpos_of_mem_quasispectrum => x ∈ quasispectrum 𝕜 a

end Quasispectrum

section Sqrt

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

lemma sqrt_def (a : A) : sqrt a = cfcₙ NNReal.sqrt a := rfl

lemma abs_def (a : A) : abs a = cfcₙ NNReal.sqrt (star a * a) := rfl

end Sqrt

section Log

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma log_def (a : A) : log a = cfc Real.log a := rfl

end Log

end CFC
