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

Some lemmas missing from Mathlib needed for the `cfc_pull` tactic.
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

/-! ### Numerals

`cfc_const` covers `algebraMap R A r`; these cover the numerals, which are `Nat.cast` and
`Int.cast` into `A`. -/

lemma cfc_natCast (n : ℕ) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (n : R)) a = (n : A) := by
  rw [cfc_const _ a ha, map_natCast]

lemma cfc_ofNat (n : ℕ) [n.AtLeastTwo] (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (OfNat.ofNat n : R)) a = (OfNat.ofNat n : A) :=
  cfc_natCast n a ha

end Unital

section IntCast

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

lemma cfc_intCast (n : ℤ) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (n : R)) a = (n : A) := by
  rw [cfc_const _ a ha, map_intCast]

end IntCast

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

section Norm

open CFC
open scoped ComplexOrder

section Unital

variable {A : Type*}
  [Ring A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsTopologicalRing A] [T2Space A]

lemma cfc_real_comp_norm [Algebra ℝ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (f : ℝ → ℝ) (a : A)
    (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' spectrum ℝ a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) :=
  cfc_comp_norm f a

lemma cfc_complex_comp_norm [Algebra ℂ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] (f : ℂ → ℂ) (a : A)
    (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' spectrum ℂ a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) :=
  cfc_comp_norm f a

/-- `CFC.abs_eq_cfcₙ_coe_norm` at `ℂ`, with the coercion `ℝ → ℂ` as it elaborates at `ℂ`, and the
unital calculus. -/
lemma CFC.abs_eq_cfc_complex_norm [Algebra ℂ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] (a : A)
    (ha : IsStarNormal a := by cfc_tac) :
    abs a = cfc (fun x : ℂ ↦ (‖x‖ : ℂ)) a :=
  -- a term, as the two coercions are only equal at default transparency
  (abs_eq_cfcₙ_coe_norm ℂ a ha).trans cfcₙ_eq_cfc

end Unital

section NonUnital

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsTopologicalRing A] [T2Space A]

lemma cfcₙ_real_comp_norm [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (f : ℝ → ℝ) (a : A)
    (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' quasispectrum ℝ a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) :=
  cfcₙ_comp_norm f a

lemma cfcₙ_complex_comp_norm [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]
    (f : ℂ → ℂ) (a : A)
    (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' quasispectrum ℂ a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) :=
  cfcₙ_comp_norm f a

/-- `CFC.abs_eq_cfcₙ_coe_norm` at `ℂ`, with the coercion `ℝ → ℂ` as it elaborates at `ℂ`. -/
lemma CFC.abs_eq_cfcₙ_complex_norm [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] (a : A)
    (ha : IsStarNormal a := by cfc_tac) :
    abs a = cfcₙ (fun x : ℂ ↦ (‖x‖ : ℂ)) a :=
  abs_eq_cfcₙ_coe_norm ℂ a ha

end NonUnital

end Norm

@[fun_prop]
lemma StarAlgHom.continuous_restrictScalars {R S A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S]
    [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B] [IsScalarTower R S A]
    [IsScalarTower R S B] [Star A] [Star B] {f : A →⋆ₐ[S] B} (hf : Continuous f) :
    Continuous (f.restrictScalars R) :=
  hf
