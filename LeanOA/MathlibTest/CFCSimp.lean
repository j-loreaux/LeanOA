/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCSimp
public import LeanOA.Mathlib.Tactic.CFCSimp.Tags
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.ComplexSqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith

/-!  # The `cfc_pull` test suite, run against `cfc_simp` -/

set_option linter.privateModule false
set_option linter.unusedVariables false
set_option warn.sorry true


section GenericUnital

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_simp R a

example (ha : p a) :
    a ^ 2 + 3 • a * cfc (id : R → R) a = cfc (fun x : R ↦ x ^ 2 + 3 • x * id x) a := by
  cfc_simp R a

example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  cfc_simp R a

example (ha : p a) (b : A) : star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv in star a * a => cfc_simp R a

example {ι : Type*} {s : Finset ι} {h : ι → R → R} (hh : ∀ i, ContinuousOn (h i) (spectrum R a)) :
    ∑ i ∈ s, star (cfc (h i) a) = cfc (∑ i ∈ s, fun x ↦ star (h i x)) a := by
  conv_lhs => enter [2, i]; cfc_simp R a
  cfc_simp R a

end GenericUnital

section GenericNonUnital

/- Here the algebra is not unital, so `cfc_pull` falls back to `cfcₙ` without being told to. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
  {a : A} {f g : R → R}

example (ha : p a) : star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  cfc_simp R a

example (ha : p a) :
    a * a + 3 • a * cfcₙ (id : R → R) a = cfcₙ (fun x : R ↦ x * x + 3 • x * id x) a := by
  cfc_simp R a

example (ha : p a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    cfcₙ f (cfcₙ g a * cfcₙ g a) = cfcₙ (fun x ↦ f (g x * g x)) a := by
  cfc_simp R a

end GenericNonUnital

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

example (ha : IsStarNormal a) : NormedSpace.exp (I • a) = cfc (fun x ↦ Complex.exp (I * x)) a := by
  cfc_simp ℂ a

example (ha : IsSelfAdjoint a) : NormedSpace.exp a = cfc Real.exp a := by cfc_simp ℝ a

example (ha : 0 ≤ a) : 1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by cfc_simp ℝ a

example (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (CFC.sqrt (a ^ 2)))) :
    CFC.sqrt (CFC.sqrt (a ^ 2)) + cfcₙ f (CFC.sqrt (a ^ 2)) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (CFC.sqrt (a ^ 2)) := by
  cfc_simp -unital ℝ≥0 (CFC.sqrt (a ^ 2))

example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_simp [CFC.sqrt_eq_cfc_complex_sqrt] ℂ a

example : a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_simp -unital ℝ a

example (ha : IsSelfAdjoint a) :
    1 - a⁺ = cfc (fun x : ℝ ↦ 1 - x⁺) a := by
  cfc_simp ℝ a

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_simp +defer ℝ≥0 a =>
    all_goals fun_prop

example (ha : IsStarNormal a) (z : ℂ) :
    NormedSpace.exp (z • a) = cfc (fun w : ℂ ↦ Complex.exp (z * w)) a := by
  cfc_simp [cfc_comp_smul] ℂ a

example (ha : IsSelfAdjoint a) :
    CFC.log (NormedSpace.exp a) = cfc (fun x : ℝ ↦ Real.log (Real.exp x)) a := by
  cfc_simp ℝ a

example (u : Aˣ) (ha : IsStarNormal (u : A)) : (↑u⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (u : A) := by
  cfc_simp ℂ (u : A)

end CStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open Complex
open scoped NNReal

example (ha : IsSelfAdjoint a) : (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by cfc_simp ℝ a

end NonUnitalCStarAlgebra

section MessySideGoals

/-! ## Side goals the auto-param tactics cannot close -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open scoped NNReal

example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_simp ℝ a =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsStrictlyPositive a) (x : ℝ) :
    a ^ x * a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ x) a := by
  cfc_simp ℝ≥0 a =>
    exact NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem ℝ≥0 ha.2))

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_simp +defer ℝ a =>
    case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
    case cfc_pull.predicate => exact ha
    case cfc_pull.continuity => fun_prop

/- The tactic-valued options take a tactic sequence, like `(disch := ..)`, and all of them may
appear in any order among the configuration items. -/
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_simp ℝ a =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_simp +zetaDelta ℝ a =>
    first | (fun_prop) | (intro x hx; exact hf0 x (hspec hx))

example (f : ℝ → ℝ) (hf : Continuous f) (hf0 : 0 = f 0) :
    cfcₙ f a + cfcₙ f a = cfcₙ (fun x ↦ f x + f x) a := by
  cfc_simp -unital ℝ a => all_goals first | (symm; exact hf0)

end MessySideGoals

section ConvSideGoals

/-! ## `=> tac`: side goals inside a `conv` block -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_simp ℝ a =>
      exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsStarNormal a) (b : A) : star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a =>
    cfc_simp +defer ℂ a =>
      -- `IsStarNormal a` is a class, so `simp` finds `ha` by instance synthesis: no predicate goal
      all_goals fun_prop

end ConvSideGoals

section LetBound

/-! ## `let`-bound variables and `+zetaDelta` -/

variable {A : Type*} [CStarAlgebra A] {a : A}

example (ha : IsStarNormal a) :
    let u : A := star a; let v : A := u * a
    v = cfc (fun x : ℂ ↦ star x * x) a := by
  extract_lets
  cfc_simp +zetaDelta ℂ a


end LetBound

section LemmaList

/-! ## `[..]`: the lemma set for one call -/

namespace LemmaListTest

variable {A : Type*} [CStarAlgebra A] {a : A}

def sq (a : A) : A := a * a

/-- … and the lemma that reads it, deliberately left untagged. -/
theorem cfc_sq (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    sq (cfc f a) = cfc (fun x ↦ f x * f x) a :=
  (cfc_mul f f a hf hf).symm


example (ha : IsStarNormal a) : sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_simp [cfc_sq] ℂ a




end LemmaListTest

end LemmaList

section Only

/-! ## `only [..]` and `cfc_pull?` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}

open scoped NNReal


example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_simp [cfc_star_id, cfc_id', cfc_mul] ℂ a


/- The suggestion replaces everything up to the element, keeping the configuration and leaving any
location or `=> ..` block as it is; lemmas used at several locations are listed once. -/

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_simp +defer [CFC.rpow_def, cfc_mul] ℝ≥0 a => all_goals fun_prop




example (ha : IsStarNormal a) (b : A) : star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a =>
    cfc_simp +defer [cfc_star_id, cfc_id', cfc_mul] ℂ a =>
      -- `IsStarNormal a` is a class, so `simp` finds `ha` by instance synthesis: no predicate goal
      all_goals fun_prop

end Only

section InTheWild

/- Goals of this shape have appeared in Mathlib. -/

open Complex
open scoped NNReal CStarAlgebra

section NonUnital

variable {A : Type*} [CStarAlgebra A] {a : A}

example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℝ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_simp ℝ (star a * a : A⁺¹)

-- this is a bit of a weird example because it pulls towards `ℝ` rather than `ℂ`.
example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℂ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_simp ℝ (star a * a : A⁺¹) =>
    rw [← IsSelfAdjoint.spectrumRestricts (by cfc_tac) |>.algebraMap_image]
    simp
  -- this is a bug with the `@[congr]` lemma `cfc_congr'`, fixed in #43689
  norm_cast
  norm_cast

end NonUnital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_simp ℂ a

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_simp ℂ a
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

/- The same, but starting from `CFC.sqrt (1 - a ^ 2)`. `cfc_pull` uses `CFC.sqrt_eq_real_sqrt`,
whose hypothesis `0 ≤ 1 - a ^ 2` becomes a side goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_simp ℂ a =>
    -- the side goal `0 ≤ 1 - a ^ 2` left by `CFC.sqrt_eq_real_sqrt`
    have key : (1 : A) - a ^ 2 = cfc (fun x : ℝ ↦ 1 - x ^ 2) a := by cfc_simp ℝ a
    rw [key]
    refine cfc_nonneg fun x hx ↦ ?_
    have hx' : |x| ≤ 1 := by
      simpa [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans ha_norm
    nlinarith [sq_abs x, abs_le.mp hx']
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

end InTheWild

/-! ## The real and imaginary parts -/

section RealImaginaryPartNonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

open Complex ComplexStarModule

example (ha : IsStarNormal a) : (ℜ a : A) = cfcₙ (fun x : ℂ ↦ (x.re : ℂ)) a := by
  cfc_simp ℂ a

example (ha : IsStarNormal a) :
    (ℜ a : A) + (ℑ a : A) = cfcₙ (fun x : ℂ ↦ (x.re : ℂ) + (x.im : ℂ)) a := by
  cfc_simp ℂ a

example (f : ℂ → ℂ) (ha : IsStarNormal a) (hf₀ : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A))) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x : ℂ ↦ f x.re) a := by
  cfc_simp ℂ a

end RealImaginaryPartNonUnital

section AbsNorm

/-! ## `cfc_comp_norm` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

example (f : ℂ → ℂ) (ha : IsStarNormal a)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℂ)) '' spectrum ℂ a)) :
    cfc f (CFC.abs a) = cfc (fun x : ℂ ↦ f ‖x‖) a := by
  cfc_simp ℂ a

example (f : ℝ → ℝ) (ha : IsSelfAdjoint a)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℝ)) '' spectrum ℝ a))
    (hf' : ContinuousOn (fun x : ℝ ↦ f ‖x‖) (spectrum ℝ a)) :
    cfc f (CFC.abs a) - a = cfc (fun x : ℝ ↦ f ‖x‖ - x) a := by
  cfc_simp ℝ a

end AbsNorm

section Tsub

/-! ## Truncated subtraction over `ℝ≥0` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open scoped NNReal

example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (spectrum ℝ≥0 a)) (hg : ContinuousOn g (spectrum ℝ≥0 a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_simp ℝ≥0 a

/- With a concrete `f` and `g` the extra hypothesis is provable, but nothing in the calculus API
is run on a `cfc_pull.side` goal, so it takes a discharger. -/
example (ha : 0 ≤ a) :
    cfc (fun x : ℝ≥0 ↦ x + 1) a - a = cfc (fun x : ℝ≥0 ↦ x + 1 - x) a := by
  cfc_simp ℝ≥0 a => all_goals first | (simp)

/- Over `ℝ` the ordinary `cfc_sub` is preferred, so no such hypothesis appears at all. -/
example (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hg : ContinuousOn g (spectrum ℝ a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_simp +defer ℝ a => all_goals assumption

example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ quasispectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 a)) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum ℝ≥0 a)) (hg0 : g 0 = 0) :
    cfcₙ f a - cfcₙ g a = cfcₙ (fun x ↦ f x - g x) a := by
  cfc_simp -unital ℝ≥0 a

end Tsub

section StarAlgHom

/-! ## Star algebra homomorphism -/

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A}
open scoped CStarAlgebra

example (φ : A →⋆ₐ[ℂ] B) (f : ℂ → ℂ) (hφ : Continuous φ) (ha : IsStarNormal a)
    (hφa : IsStarNormal (φ a)) (hf : ContinuousOn f (spectrum ℂ a)) :
    φ (cfc f a) = cfc f (φ a) := by
  cfc_simp ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (f : ℝ → ℝ) (ha : IsSelfAdjoint a)
    (hf₁ : ContinuousOn f (quasispectrum ℝ a)) (hf0 : f 0 = 0) :
    φ (cfcₙ f a) = cfcₙ f (φ a) := by
  -- uses `NonUnitalStarAlgHomClass.map_cfcₙ` with `S := ℝ`, `R := ℂ`, and `F := A →⋆ₐ[ℂ] B`.
  cfc_simp -unital ℝ (φ a)

example {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)
    (f g : ℂ → ℂ) (ha : IsStarNormal a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_simp -unital ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (f g : ℝ → ℝ) (ha : IsSelfAdjoint a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_simp ℂ (φ a)
  simp

example (φ : A →⋆ₐ[ℂ] B) (f g : ℝ → ℝ) (ha : IsSelfAdjoint a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_simp ℝ (φ a)

/- The argument of `φ` need not already be an application of the calculus: it is pulled towards
`a` in `A`, and the result carried through `φ`. -/
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) :
    φ (star a * a) = cfc (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_simp ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) :
    star (φ (a ^ 2)) * φ a = cfc (fun x : ℂ ↦ star (x ^ 2) * x) (φ a) := by
  cfc_simp ℂ (φ a)

/- Two homomorphisms deep: the recursion descends through `ψ` and then through `φ`. -/
example {C : Type*} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (ha : IsStarNormal a) :
    ψ (φ (star a * a)) = cfc (fun x : ℂ ↦ star x * x) (ψ (φ a)) := by
  cfc_simp ℂ (ψ (φ a))

end StarAlgHom

section NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] {a : A}

open scoped CStarAlgebra

example (φ : A →⋆ₙₐ[ℂ] B) (ha : IsStarNormal a) :
    φ (star a * a) = cfcₙ (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_simp ℂ (φ a)

example (φ : A⁺¹ →⋆ₙₐ[ℂ] B) (ha : IsStarNormal a) (hφa : IsStarNormal (φ a)) :
    φ (star a * a) = cfcₙ (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_simp ℂ (φ a)

end NonUnitalStarAlgHom

section Unitization

/-! ## The unitization -/

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

/- What sits under the coercion is pulled in `A`, in the non-unital calculus, and then bridged. -/
example (ha : IsStarNormal a) :
    ((star a * a : A) : Unitization ℂ A) = cfc (fun x : ℂ ↦ star x * x) (a : Unitization ℂ A) := by
  cfc_simp ℂ (a : Unitization ℂ A)

example (ha : IsStarNormal a) :
    (1 : Unitization ℂ A) - ((star a * a : A) : Unitization ℂ A) =
      cfc (fun x : ℂ ↦ 1 - star x * x) (a : Unitization ℂ A) := by
  cfc_simp ℂ (a : Unitization ℂ A)

end Unitization


/-! # `at` -/

variable {A : Type*} [CStarAlgebra A] {a b : A}


example (ha : IsStarNormal a) (h : star a * a = b) : cfc (fun x : ℂ ↦ star x * x) a = b := by
  cfc_simp ℂ a at h
  exact h

example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_simp ℂ a at h ⊢
  exact h

example (ha : IsStarNormal a) (h : star a * a = a) :
    cfc (fun x : ℂ ↦ star x * x) a = cfc (fun x : ℂ ↦ x) a := by
  cfc_simp ℂ a at h
  exact h

example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_simp ℂ a at *
  exact h

/- Side goals raised at a hypothesis go to the `=> ..` block too. -/
example [PartialOrder A] [StarOrderedRing A] (ha : IsStrictlyPositive a)
    (h : CFC.log a * CFC.log a = b) : cfc (fun x : ℝ ↦ Real.log x * Real.log x) a = b := by
  cfc_simp ℝ a at h =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)
  exact h
