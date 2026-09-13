/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull
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

/-!  # Test suite for the `cfc_pull` tactic -/

set_option linter.privateModule false

section GenericUnital

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a

example (ha : p a) :
    a ^ 2 + 3 • a * cfc (id : R → R) a = cfc (fun x : R ↦ x ^ 2 + 3 • x * id x) a := by
  cfc_pull R a

example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  cfc_pull R a

example (ha : p a) (b : A) : star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv in star a * a => cfc_pull R a

example {ι : Type*} {s : Finset ι} {h : ι → R → R} (hh : ∀ i, ContinuousOn (h i) (spectrum R a)) :
    ∑ i ∈ s, star (cfc (h i) a) = cfc (∑ i ∈ s, fun x ↦ star (h i x)) a := by
  conv_lhs => enter [2, i]; cfc_pull R a
  cfc_pull R a

end GenericUnital

section GenericNonUnital

/- Here the algebra is not unital, so `cfc_pull` falls back to `cfcₙ` without being told to. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
  {a : A} {f g : R → R}

example (ha : p a) : star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  cfc_pull R a

example (ha : p a) :
    a * a + 3 • a * cfcₙ (id : R → R) a = cfcₙ (fun x : R ↦ x * x + 3 • x * id x) a := by
  cfc_pull R a

example (ha : p a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    cfcₙ f (cfcₙ g a * cfcₙ g a) = cfcₙ (fun x ↦ f (g x * g x)) a := by
  cfc_pull R a

end GenericNonUnital

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

example (ha : IsStarNormal a) : NormedSpace.exp (I • a) = cfc (fun x ↦ Complex.exp (I * x)) a := by
  cfc_pull ℂ a

example (ha : IsSelfAdjoint a) : NormedSpace.exp a = cfc Real.exp a := by cfc_pull ℝ a

example (ha : 0 ≤ a) : 1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by cfc_pull ℝ a

example (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (CFC.sqrt (a ^ 2)))) :
    CFC.sqrt (CFC.sqrt (a ^ 2)) + cfcₙ f (CFC.sqrt (a ^ 2)) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (CFC.sqrt (a ^ 2)) := by
  cfc_pull -unital ℝ≥0 (CFC.sqrt (a ^ 2))

example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_pull [CFC.sqrt_eq_cfc_complex_sqrt] ℂ a

example : a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull -unital ℝ a

example (ha : IsSelfAdjoint a) :
    1 - a⁺ = cfc (fun x : ℝ ↦ 1 - x⁺) a := by
  cfc_pull ℝ a

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull +deferAll ℝ≥0 a <;> fun_prop

example (ha : IsStarNormal a) (z : ℂ) :
    NormedSpace.exp (z • a) = cfc (fun w : ℂ ↦ Complex.exp (z * w)) a := by
  cfc_pull [cfc_comp_smul] ℂ a

example (ha : IsSelfAdjoint a) :
    CFC.log (NormedSpace.exp a) = cfc (fun x : ℝ ↦ Real.log (Real.exp x)) a := by
  cfc_pull ℝ a

example (u : Aˣ) (ha : IsStarNormal (u : A)) : (↑u⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (u : A) := by
  cfc_pull ℂ (u : A)

end CStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open Complex
open scoped NNReal

example (ha : IsSelfAdjoint a) : (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by cfc_pull ℝ a

end NonUnitalCStarAlgebra

section MessySideGoals

/-! ## Side goals the auto-param tactics cannot close -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open scoped NNReal

example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull ℝ a =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsStrictlyPositive a) (x : ℝ) :
    a ^ x * a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ x) a := by
  cfc_pull ℝ≥0 a =>
    exact NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem ℝ≥0 ha.2))

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull +deferAll ℝ a =>
    case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
    case cfc_pull.predicate => exact ha
    case cfc_pull.continuity => fun_prop

end MessySideGoals

section ConvSideGoals

/-! ## `=> tac`: side goals inside a `conv` block -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_pull ℝ a =>
      exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsStarNormal a) (b : A) : star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a => cfc_pull +deferAll ℂ a =>
    case cfc_pull.predicate => exact ha
    all_goals fun_prop

end ConvSideGoals

section LetBound

/-! ## `let`-bound variables and `+zetaDelta` -/

variable {A : Type*} [CStarAlgebra A] {a : A}

example (ha : IsStarNormal a) :
    let u : A := star a; let v : A := u * a
    v = cfc (fun x : ℂ ↦ star x * x) a := by
  extract_lets
  cfc_pull +zetaDelta ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `v`
    (head symbol: _, target: cfc over ℂ at `a`)
  `v` is a local definition, and `cfc_pull` does not look
  at what it stands for. Unfold it with `cfc_pull +zetaDelta ..`, or rewrite it away
  first — `set .. with h` hands you the equation `h` to do it with.
-/
#guard_msgs in
example (ha : IsStarNormal a) :
    let u : A := star a; let v : A := u * a
    v = cfc (fun x : ℂ ↦ star x * x) a := by
  extract_lets u v
  cfc_pull ℂ a

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

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `sq a`
    (head symbol: LemmaListTest.sq, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) : sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [cfc_sq] ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `a * a`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul, -cfcₙ_mul] ℂ a


set_option trace.Tactic.cfc_pull true in
/--
trace: [Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull a * a into a cfc over ℂ
  [Tactic.cfc_pull] candidates: [cfcₙ_mul]
  [Tactic.cfc_pull] ✅️ cfcₙ_mul
    [Tactic.cfc_pull] predicate for cfcₙ over ℂ is IsStarNormal
    [Tactic.cfc_pull] ✅️ pull a into a cfcₙ over ℂ
      [Tactic.cfc_pull] ✅️ cfc_id'
        [Tactic.cfc_pull] filled `IsStarNormal a` from the shared predicate proof
        [Tactic.cfc_pull] ✅️ cfcₙ_eq_cfc
          [Tactic.cfc_pull] deferred `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)`
          [Tactic.cfc_pull] deferred `0 = 0`
    [Tactic.cfc_pull] ✅️ pull a into a cfcₙ over ℂ
      [Tactic.cfc_pull] ✅️ cfc_id'
        [Tactic.cfc_pull] filled `IsStarNormal a` from the shared predicate proof
        [Tactic.cfc_pull] ✅️ cfcₙ_eq_cfc
          [Tactic.cfc_pull] deferred `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)`
          [Tactic.cfc_pull] deferred `0 = 0`
    [Tactic.cfc_pull] deferred `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)`
    [Tactic.cfc_pull] deferred `0 = 0`
    [Tactic.cfc_pull] deferred `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)`
    [Tactic.cfc_pull] deferred `0 = 0`
    [Tactic.cfc_pull] ✅️ cfcₙ_eq_cfc
      [Tactic.cfc_pull] deferred `ContinuousOn (fun x ↦ x * x) (quasispectrum ℂ a)`
      [Tactic.cfc_pull] deferred `0 * 0 = 0`
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ x * x) a into a cfc over ℂ
  [Tactic.cfc_pull] ✅️ the calculus already applied at a
[Tactic.cfc_pull] ✅️ closed `IsStarNormal a` with `assumption`
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0 = 0` with `cfc_zero_tac`
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0 = 0` with `cfc_zero_tac`
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0 = 0` with `cfc_zero_tac`
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x) (quasispectrum ℂ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0 = 0` with `cfc_zero_tac`
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x * x) (quasispectrum ℂ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0 * 0 = 0` with `cfc_zero_tac`
-/
#guard_msgs in
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul] ℂ a

end LemmaListTest

end LemmaList

section InTheWild

/- Goals of this shape have appeared in Mathlib. -/

open Complex
open scoped NNReal CStarAlgebra

section NonUnital

variable {A : Type*} [CStarAlgebra A] {a : A}

example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℝ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull ℝ (star a * a : A⁺¹)

-- this is a bit of a weird example because it pulls towards `ℝ` rather than `ℂ`.
example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℂ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull ℝ (star a * a : A⁺¹) =>
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
  cfc_pull ℂ a

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

/- The same, but starting from `CFC.sqrt (1 - a ^ 2)`. `cfc_pull` uses `CFC.sqrt_eq_real_sqrt`,
whose hypothesis `0 ≤ 1 - a ^ 2` becomes a side goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a =>
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

/-! ## The real and imaginary parts -/

section RealImaginaryPartNonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

open Complex ComplexStarModule

example (ha : IsStarNormal a) : (ℜ a : A) = cfcₙ (fun x : ℂ ↦ (x.re : ℂ)) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) :
    (ℜ a : A) + (ℑ a : A) = cfcₙ (fun x : ℂ ↦ (x.re : ℂ) + (x.im : ℂ)) a := by
  cfc_pull ℂ a

example (f : ℂ → ℂ) (ha : IsStarNormal a) (hf₀ : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A))) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x : ℂ ↦ f x.re) a := by
  cfc_pull ℂ a

end RealImaginaryPartNonUnital

section AbsNorm

/-! ## `cfc_comp_norm` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

example (f : ℂ → ℂ) (ha : IsStarNormal a)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℂ)) '' spectrum ℂ a)) :
    cfc f (CFC.abs a) = cfc (fun x : ℂ ↦ f ‖x‖) a := by
  cfc_pull ℂ a

example (f : ℝ → ℝ) (ha : IsSelfAdjoint a)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℝ)) '' spectrum ℝ a))
    (hf' : ContinuousOn (fun x : ℝ ↦ f ‖x‖) (spectrum ℝ a)) :
    cfc f (CFC.abs a) - a = cfc (fun x : ℝ ↦ f ‖x‖ - x) a := by
  cfc_pull ℝ a

end AbsNorm

section Tsub

/-! ## Truncated subtraction over `ℝ≥0` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open scoped NNReal

example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (spectrum ℝ≥0 a)) (hg : ContinuousOn g (spectrum ℝ≥0 a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull ℝ≥0 a

/- With a concrete `f` and `g` the extra hypothesis is provable, but nothing in the calculus API
is run on a `cfc_pull.side` goal, so it takes a discharger. -/
example (ha : 0 ≤ a) :
    cfc (fun x : ℝ≥0 ↦ x + 1) a - a = cfc (fun x : ℝ≥0 ↦ x + 1 - x) a := by
  cfc_pull (disch := simp) ℝ≥0 a

/- Over `ℝ` the ordinary `cfc_sub` is preferred, so no such hypothesis appears at all. -/
example (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hg : ContinuousOn g (spectrum ℝ a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull +deferAll ℝ a <;> assumption

example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ quasispectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 a)) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum ℝ≥0 a)) (hg0 : g 0 = 0) :
    cfcₙ f a - cfcₙ g a = cfcₙ (fun x ↦ f x - g x) a := by
  cfc_pull -unital ℝ≥0 a

end Tsub

section StarAlgHom

/-! ## Star algebra homomorphism -/

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A}
open scoped CStarAlgebra

example (φ : A →⋆ₐ[ℂ] B) (f : ℂ → ℂ) (hφ : Continuous φ) (ha : IsStarNormal a)
    (hφa : IsStarNormal (φ a)) (hf : ContinuousOn f (spectrum ℂ a)) :
    φ (cfc f a) = cfc f (φ a) := by
  cfc_pull ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (f : ℝ → ℝ) (ha : IsSelfAdjoint a)
    (hf₁ : ContinuousOn f (quasispectrum ℝ a)) (hf0 : f 0 = 0) :
    φ (cfcₙ f a) = cfcₙ f (φ a) := by
  -- uses `NonUnitalStarAlgHomClass.map_cfcₙ` with `S := ℝ`, `R := ℂ`, and `F := A →⋆ₐ[ℂ] B`.
  cfc_pull -unital ℝ (φ a)

example {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (φ : F)
    (f g : ℂ → ℂ) (ha : IsStarNormal a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_pull -unital ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (f g : ℝ → ℝ) (ha : IsSelfAdjoint a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_pull ℂ (φ a)
  simp

example (φ : A →⋆ₐ[ℂ] B) (f g : ℝ → ℝ) (ha : IsSelfAdjoint a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : Continuous g) (hg0 : g 0 = 0) :
    star (φ (cfcₙ f a)) * (φ (cfc g a)) =
      φ (cfcₙ (fun x ↦ star (f x) * (g x)) a) := by
  cfc_pull ℝ (φ a)

/- The argument of `φ` need not already be an application of the calculus: it is pulled towards
`a` in `A`, and the result carried through `φ`. -/
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) :
    φ (star a * a) = cfc (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_pull ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) :
    star (φ (a ^ 2)) * φ a = cfc (fun x : ℂ ↦ star (x ^ 2) * x) (φ a) := by
  cfc_pull ℂ (φ a)

/- Two homomorphisms deep: the recursion descends through `ψ` and then through `φ`. -/
example {C : Type*} [CStarAlgebra C] (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (ha : IsStarNormal a) :
    ψ (φ (star a * a)) = cfc (fun x : ℂ ↦ star x * x) (ψ (φ a)) := by
  cfc_pull ℂ (ψ (φ a))

end StarAlgHom

section NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] {a : A}

open scoped CStarAlgebra

example (φ : A →⋆ₙₐ[ℂ] B) (ha : IsStarNormal a) :
    φ (star a * a) = cfcₙ (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_pull ℂ (φ a)

example (φ : A⁺¹ →⋆ₙₐ[ℂ] B) (ha : IsStarNormal a) (hφa : IsStarNormal (φ a)) :
    φ (star a * a) = cfcₙ (fun x : ℂ ↦ star x * x) (φ a) := by
  cfc_pull ℂ (φ a)

end NonUnitalStarAlgHom

section Unitization

/-! ## The unitization -/

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

/- What sits under the coercion is pulled in `A`, in the non-unital calculus, and then bridged. -/
example (ha : IsStarNormal a) :
    ((star a * a : A) : Unitization ℂ A) = cfc (fun x : ℂ ↦ star x * x) (a : Unitization ℂ A) := by
  cfc_pull ℂ (a : Unitization ℂ A)

example (ha : IsStarNormal a) :
    (1 : Unitization ℂ A) - ((star a * a : A) : Unitization ℂ A) =
      cfc (fun x : ℂ ↦ 1 - star x * x) (a : Unitization ℂ A) := by
  cfc_pull ℂ (a : Unitization ℂ A)

end Unitization

/-! ## Failures -/

/--
error: `@[cfc_pull]` failed: `cfc_comp_re` changes both the scalar ring and the
element of the functional calculus; such lemmas are not supported.
-/
#guard_msgs in
attribute [cfc_pull] cfc_comp_re


variable {A : Type*} [CStarAlgebra A] {a b : A}

/--
error: `@[cfc_pull]` failed: neither side of `Nat.add_comm` has `cfc` or `cfcₙ`
as its head symbol:
  ?n + ?m = ?m + ?n
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [Nat.add_comm] ℂ a

/--
error: `hf` is a local hypothesis, and `cfc_pull`'s lemma list takes declaration names only: a
  `@[cfc_pull]` lemma is instantiated from its constant, so there is nothing for a hypothesis to
  be. Rewrite with it first, as in `rw [hf]`.
-/
#guard_msgs (whitespace := lax) in
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : star a = cfc f a) :
    star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [hf] ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `star b * b`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : star b * b = star b * b := by
  cfc_pull +deferAll ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull`: `A` has no non-unital continuous functional calculus over `ℚ`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull ℚ a

/--
error: `cfc_pull` found nothing of type `A` in the goal
  2 = 2
-/
#guard_msgs in
example (ha : IsStarNormal a) : (2 : ℕ) = 2 := by
  cfc_pull ℂ a

/--
error: `cfc_pull` rewrote the goal but could not discharge 1 side goal:
  case cfc_pull.predicate
  A : Type u_1
  inst✝ : CStarAlgebra A
  a b : A
  ⊢ IsStarNormal a
Discharge them with a tactic block, as in `cfc_pull .. => tac`.
-/
#guard_msgs in
example : cfc (fun x : ℂ ↦ x) a = a := by
  cfc_pull ℂ a

/--
error: `cfc_pull` ran the `=> ..` block, but 1 side goal is still open:
  case cfc_pull.predicate
  A : Type u_1
  inst✝ : CStarAlgebra A
  a b : A
  ⊢ IsStarNormal a
The `=> ..` block must close every side goal.
-/
#guard_msgs in
example : cfc (fun x : ℂ ↦ x) a = a := by
  cfc_pull ℂ a => skip

/-! # Tracing -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull 3 • a into a cfc over ℂ
  [Tactic.cfc_pull] candidates: [cfc_const_mul_id,
       cfc_const_mul,
       cfc_smul_id,
       cfc_smul,
       cfcₙ_const_mul_id,
       cfcₙ_const_mul,
       cfcₙ_smul_id,
       cfcₙ_smul]
  [Tactic.cfc_pull] ❌️ cfc_const_mul_id: does not match: `?r • a` ≠ `3 • a`
  [Tactic.cfc_pull] ❌️ cfc_const_mul: does not match: `?r • ?_` ≠ `3 • a`
  [Tactic.cfc_pull] ✅️ cfc_smul_id
    [Tactic.cfc_pull] filled `IsStarNormal a` from the shared predicate proof
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ 3 • x) a into a cfc over ℂ
  [Tactic.cfc_pull] ✅️ the calculus already applied at a
[Tactic.cfc_pull] ✅️ closed `IsStarNormal a` with `assumption`
-/
-- `pp.mvars.anonymous false` so that the unnamed metavariable in the rejected pattern prints as
-- `?_` rather than with an index that every edit above this point would shift
#guard_msgs in
set_option pp.mvars.anonymous false in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStarNormal a) : (3 : ℕ) • a = cfc (fun x : ℂ ↦ (3 : ℕ) • x) a := by
  cfc_pull ℂ a

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull CFC.log a * CFC.log a into a cfc over ℝ
  [Tactic.cfc_pull] candidates: [cfc_mul, cfcₙ_mul]
  [Tactic.cfc_pull] ✅️ cfc_mul
    [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
      [Tactic.cfc_pull] candidates: [CFC.log_def]
      [Tactic.cfc_pull] ✅️ CFC.log_def
    [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
      [Tactic.cfc_pull] candidates: [CFC.log_def]
      [Tactic.cfc_pull] ✅️ CFC.log_def
    [Tactic.cfc_pull] deferred `ContinuousOn Real.log (spectrum ℝ a)`
    [Tactic.cfc_pull] deferred `ContinuousOn Real.log (spectrum ℝ a)`
[Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ Real.log x * Real.log x) a into a cfc over ℝ
  [Tactic.cfc_pull] ✅️ the calculus already applied at a
[Tactic.cfc_pull] ❌️ could not close `ContinuousOn Real.log (spectrum ℝ a)`
[Tactic.cfc_pull] side goal `ContinuousOn Real.log (spectrum ℝ a)` is a duplicate
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example [PartialOrder A] [StarOrderedRing A] (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull ℝ a =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)
