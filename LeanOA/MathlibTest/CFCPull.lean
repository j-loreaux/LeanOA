/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull.Core
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith

/-!  # Test suite for the `cfc_pull` tactic -/

set_option linter.privateModule false
set_option linter.unusedVariables false
set_option warn.sorry true

section GenericUnital

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a

example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  cfc_pull R a

example {ι : Type*} {s : Finset ι} {h : ι → R → R} (hh : ∀ i, ContinuousOn (h i) (spectrum R a)) :
    ∑ i ∈ s, star (cfc (h i) a) = cfc (∑ i ∈ s, fun x ↦ star (h i x)) a := by
  cfc_pull R a

end GenericUnital

section GenericNonUnital

/- Here the algebra is not unital, so `cfc_pull` falls back to `cfcₙ` without being told to. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {a : A}

example (ha : p a) : star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  cfc_pull R a

end GenericNonUnital

section CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B]
  {a b : A}

open Complex
open scoped NNReal

example (ha : IsStarNormal a) : NormedSpace.exp (I • a) = cfc (fun x ↦ Complex.exp (I * x)) a := by
  cfc_pull ℂ a

example (ha : 0 ≤ a) : 1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by cfc_pull ℝ a

example : a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull -unital ℝ a

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull +defer ℝ≥0 a =>
    all_goals fun_prop

example (u : Aˣ) (ha : IsStarNormal (u : A)) : (↑u⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (u : A) := by
  cfc_pull ℂ (u : A)

example (ha : IsStarNormal a) : CFC.abs a * a = cfc (fun x : ℂ ↦ (‖x‖ : ℂ) * x) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) : (2 : A) * a = cfc (fun x : ℂ ↦ 2 * x) a := by cfc_pull ℂ a

example (ha : IsSelfAdjoint a) (n : ℤ) : n * a = cfc (fun x : ℝ ↦ n * x) a := by cfc_pull ℝ a

/- `cfc_tsub` asks for `g ≤ f` on the spectrum; over `ℝ` the ordinary `cfc_sub` is preferred, so
no such hypothesis appears at all. -/
example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (spectrum ℝ≥0 a)) (hg : ContinuousOn g (spectrum ℝ≥0 a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull ℝ≥0 a

example (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hg : ContinuousOn g (spectrum ℝ a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull +defer ℝ a => all_goals assumption

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull +defer ℝ a =>
    case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
    case cfc_pull.predicate => exact ha
    case cfc_pull.continuity => fun_prop

/- `(disch := ..)` is for the `cfc_pull.side` goals, here `∀ x ∈ spectrum ℝ a, f x ≠ 0`. -/
example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull (disch := grind) ℝ a

example (f : ℝ → ℝ) (hf : Continuous f) (hf0 : 0 = f 0) :
    cfcₙ f a + cfcₙ f a = cfcₙ (fun x ↦ f x + f x) a := by
  cfc_pull -unital ℝ a => all_goals first | (symm; exact hf0)

example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_pull ℝ a =>
      exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsStarNormal a) (h : star a * a = b) : cfc (fun x : ℂ ↦ star x * x) a = b := by
  cfc_pull ℂ a at h
  exact h

example (ha : IsStrictlyPositive a) (h : CFC.log a * CFC.log a = b) :
    CFC.log a * CFC.log a = b := by
  cfc_pull ℝ a at h ⊢ =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)
  exact h

/- Each subexpression is pulled towards the element it is an expression in, and a constant towards
the element its neighbours are at. -/
example (ha : IsStarNormal a) (hb : IsStarNormal b) :
    (a * a + 1) * (2 + b + (1 + 1)) =
      cfc (fun x : ℂ ↦ x * x + 1) a * cfc (fun x : ℂ ↦ 2 + x + (1 + 1)) b := by
  cfc_pull ℂ a b

/- Standing alone, it is left as it is when there are multiple targets. -/
example (ha : IsStarNormal a) (hb : IsStarNormal b) (c : A) (h : c = 1 + 1) : (1 : A) + 1 = c := by
  fail_if_success cfc_pull ℂ a b
  exact h.symm

def LemmaListTest.sq (a : A) : A := a * a

/-- The lemma that reads `sq`, deliberately left untagged. -/
theorem LemmaListTest.cfc_sq {A : Type*} [CStarAlgebra A] (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    sq (cfc f a) = cfc (fun x ↦ f x * f x) a :=
  (cfc_mul f f a hf hf).symm

example (ha : IsStarNormal a) : LemmaListTest.sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull ℂ a [LemmaListTest.cfc_sq]

/- A hypothesis is a rewrite rule like any other; here it outranks `cfc_star_id`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : star a = cfc f a) (hf' : Continuous f) :
    star a * a = cfc (fun x ↦ f x * x) a := by
  cfc_pull ℂ a [hf]

/--
info: Try this:
  [apply] cfc_pull ℂ a only [hg 2, hg _, cfc_mul]
-/
#guard_msgs in
example (ha : IsStarNormal a) (g : ℕ → A) (hg : ∀ n, g n = cfc (fun x : ℂ ↦ x ^ n) a) :
    g 2 * g 3 = cfc (fun x : ℂ ↦ x ^ 2 * x ^ 3) a := by
  cfc_pull? ℂ a [hg 2, hg _]

/--
info: Try this:
  [apply] cfc_pull ℂ a only [cfc_id', cfc_mul, cfc_add, cfc_star_id, LemmaListTest.sq, hb, ← hc, u]
-/
#guard_msgs in
example (ha : IsStarNormal a) (b c : A) (hb : b = a * a) (hc : star a = c) :
    let u : A := LemmaListTest.sq a * a
    u + b + c = cfc (fun x : ℂ ↦ x * x * x + x * x + star x) a := by
  extract_lets u
  cfc_pull? ℂ a [LemmaListTest.sq, hb, ← hc, u]

/--
error: `cfc_pull`: both sides of `h` are the same calculus applied to the same element; there is nothing for `cfc_pull` to do with it
-/
#guard_msgs in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) (h : cfc f a = cfc g a) : cfc f a = cfc g a := by
  cfc_pull ℂ a [h]

/--
info: Try this:
  [apply] cfc_pull +defer ℝ≥0 a only [CFC.rpow_def, cfc_mul]
-/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull? +defer ℝ≥0 a => all_goals fun_prop

/--
info: Try this:
  [apply] cfc_pull ℂ a only [cfc_id', cfc_star_id, cfc_mul]
-/
#guard_msgs in
example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_pull? ℂ a at *
  exact h

/- `cfc_const` mentions the element only on its calculus side, so it is instantiated at the
target like `cfc_const_one`. -/
example (ha : IsStarNormal a) (z : ℂ) : algebraMap ℂ A z * a = cfc (fun x : ℂ ↦ z * x) a := by
  cfc_pull ℂ a

/- A lemma generic in its ring is specialized to the ring asked for before it is matched: the
real scalar is pulled as `t • x`, not as `↑(t * x.re)` through the real calculus. -/
example (ha : IsStarNormal a) (t : ℝ) : t • a = cfc (fun x : ℂ ↦ t • x) a := by cfc_pull ℂ a

/- The inner element of `cfc g (a ^ 2 + a)` is pulled before composing, so that the composition
happens at `a`, whose predicate is known, rather than at `a ^ 2 + a`. -/
example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    cfc f (cfc g (a ^ 2 + a)) = cfc (fun x : ℂ ↦ f (g (x ^ 2 + x))) a := by
  cfc_pull ℂ a

/- The target may itself be an application of the calculus. -/
example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    cfc g (cfc f a) * cfc f a = cfc (fun x : ℂ ↦ g x * x) (cfc f a) := by
  cfc_pull ℂ (cfc f a)

/- Inside the calculus, an inner element that does not become the calculus applied to something
is left alone: `cfc f (a + b)` does not become `cfc f (cfc id a + b)`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (b : A) :
    cfc f (a + b) * a = cfc f (a + b) * cfc (fun x : ℂ ↦ x) a := by
  cfc_pull ℂ a

/- Only towards the target: what is an expression in another element is left alone. -/
example (ha : IsStarNormal a) :
    star b * a ^ 2 + (3 : ℂ) • b = star b * cfc (fun x : ℂ ↦ x ^ 2) a + (3 : ℂ) • b := by
  cfc_pull ℂ a

/- The shortcut `r • a = cfc (r * ·) a` is not taken at `r • a ^ 2`, where it would ask for the
predicate at `a ^ 2`; with nothing deferred to it, the `=> ..` block has nothing to do. -/
example (ha : IsStarNormal a) : (3 : ℂ) • a ^ 2 = cfc (fun x : ℂ ↦ 3 * x ^ 2) a := by
  cfc_pull ℂ a => skip

end CStarAlgebra

section Structured

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A}

open scoped CStarAlgebra

example {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)
    (f g : ℂ → ℂ) (ha : IsStarNormal a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_pull -unital ℂ (φ a)

example {C : Type*} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (ha : IsStarNormal a) :
    ψ (φ (star a * a)) = cfc (fun x : ℂ ↦ star x * x) (ψ (φ a)) := by
  cfc_pull ℂ (ψ (φ a))

/- occasionally, `cfc_pull -unital` results in *fewer* side goals, but this is uncommon. -/
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) (hφ : Continuous φ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (quasispectrum ℂ a)) (hf0 : f 0 = 0) :
    φ (cfcₙ f a) = cfcₙ f (φ a) := by
  cfc_pull -unital ℂ (φ a)

/--
info: Try this:
  [apply] cfc_pull ℂ (φ a) only [StarAlgHom.map_cfc]
-/
#guard_msgs in
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) (hφ : Continuous φ) (f : ℂ → ℂ)
    (hf : Continuous f) : φ (cfc f a) = cfc f (φ a) := by
  cfc_pull? ℂ (φ a)

example (c : B) (hac : IsStarNormal (a, c)) (ha : IsStarNormal a) (hc : IsStarNormal c) :
    (star a * a, star c * c) = cfc (fun x : ℂ ↦ star x * x) (a, c) := by
  cfc_pull ℂ (a, c)

/- A homomorphism is pulled through only towards a target: not towards `φ a` when it is `a`. -/
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) (f : ℂ → ℂ) (h : φ (cfc f a) = 0) :
    φ (cfc f a) = 0 := by
  fail_if_success cfc_pull ℂ a
  exact h

end Structured

section NonUnitalCStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] {a : A}

open ComplexStarModule
open scoped CStarAlgebra

example (ha : IsSelfAdjoint a) : (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by cfc_pull ℝ a

example (f : ℂ → ℂ) (ha : IsStarNormal a) (hf₀ : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A))) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x : ℂ ↦ f x.re) a := by
  cfc_pull ℂ a

example (φ : A →⋆ₙₐ[ℂ] B) (ha : IsStarNormal a) :
    φ (star a * a) = cfcₙ (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_pull ℂ (φ a)

example (ha : IsStarNormal a) :
    (1 : Unitization ℂ A) - ((star a * a : A) : Unitization ℂ A) =
      cfc (fun x : ℂ ↦ 1 - star x * x) (a : Unitization ℂ A) := by
  cfc_pull ℂ (a : Unitization ℂ A)

end NonUnitalCStarAlgebra

section InTheWild

open Complex
open scoped NNReal CStarAlgebra

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℝ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull ℝ (star a * a : A⁺¹)

end NonUnital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  conv_lhs => cfc_pull ℝ a; cfc_pull ℂ a

/- The same, but starting from `CFC.sqrt (1 - a ^ 2)`. `cfc_pull` uses `CFC.sqrt_eq_real_sqrt`,
whose hypothesis `0 ≤ 1 - a ^ 2` becomes a side goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a only [cfc_id', CFC.sqrt_eq_real_sqrt, cfc_const_one, cfc_pow_id, cfc_sub,
    cfcₙ_eq_cfc, cfc_comp', cfc_real_eq_complex, cfc_const_mul, cfc_add] =>
    -- the side goal `0 ≤ 1 - a ^ 2` left by `CFC.sqrt_eq_real_sqrt`
    have key : (1 : A) - a ^ 2 = cfc (fun x : ℝ ↦ 1 - x ^ 2) a := by cfc_pull ℝ a
    rw [key]
    refine cfc_nonneg fun x hx ↦ ?_
    have hx' : |x| ≤ 1 := by
      simpa [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans ha_norm
    nlinarith [sq_abs x, abs_le.mp hx']
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

end InTheWild
