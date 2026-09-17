/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.ComplexSqrt
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
  cfc_pull +defer ℝ≥0 a =>
    all_goals fun_prop

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
  cfc_pull +defer ℝ a =>
    case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
    case cfc_pull.predicate => exact ha
    case cfc_pull.continuity => fun_prop

/- The tactic-valued options take a tactic sequence, like `(disch := ..)`, and all of them may
appear in any order among the configuration items. -/
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull ℝ a =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull ℝ a =>
    first | (fun_prop) | (intro x hx; exact hf0 x (hspec hx))

example (f : ℝ → ℝ) (hf : Continuous f) (hf0 : 0 = f 0) :
    cfcₙ f a + cfcₙ f a = cfcₙ (fun x ↦ f x + f x) a := by
  cfc_pull -unital ℝ a => all_goals first | (symm; exact hf0)

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
  conv in star a * a =>
    cfc_pull +defer ℂ a =>
      -- `IsStarNormal a` is a class, so `simp` finds `ha` by instance synthesis: no predicate goal
      all_goals fun_prop

end ConvSideGoals

section LetBound

/-! ## `let`-bound variables are unfolded when listed, as by `simp` -/

variable {A : Type*} [CStarAlgebra A] {a : A}

example (ha : IsStarNormal a) :
    let u : A := star a; let v : A := u * a
    v = cfc (fun x : ℂ ↦ star x * x) a := by
  extract_lets u v
  cfc_pull [u, v] ℂ a

/--
info: Try this:
  [apply] cfc_pull only [cfc_star_id, cfc_id', cfc_mul, v, u] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) :
    let u : A := star a; let v : A := u * a
    v = cfc (fun x : ℂ ↦ star x * x) a := by
  extract_lets u v
  cfc_pull? [u, v] ℂ a

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
  cfc_pull [cfc_sq] ℂ a




end LemmaListTest

/-! ### Local hypotheses in the lemma list -/

section Hypotheses

variable {A : Type*} [CStarAlgebra A] {a : A}

/- A hypothesis is a rewrite rule like any other; here it outranks `cfc_star_id`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : star a = cfc f a) (hf' : Continuous f) :
    star a * a = cfc (fun x ↦ f x * x) a := by
  cfc_pull [hf] ℂ a

/- With the calculus on the left: a composition with the inner element `a ^ 2`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : Continuous f)
    (h : cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a) :
    cfc f (a ^ 2) + a = cfc (fun x ↦ f (x ^ 2) + x) a := by
  cfc_pull [h] ℂ a

/- Quantified hypotheses work too. -/
example (ha : IsStarNormal a) (g : ℕ → A) (hg : ∀ n, g n = cfc (fun x : ℂ ↦ x ^ n) a) :
    g 2 * g 3 = cfc (fun x : ℂ ↦ x ^ 2 * x ^ 3) a := by
  cfc_pull [hg] ℂ a

/- As do terms. -/
example (ha : IsStarNormal a) (g : ℕ → A) (hg : ∀ n, g n = cfc (fun x : ℂ ↦ x ^ n) a) :
    g 2 * g 3 = cfc (fun x : ℂ ↦ x ^ 2 * x ^ 3) a := by
  cfc_pull [hg 2, hg _] ℂ a

/--
info: Try this:
  [apply] cfc_pull only [hg 2, hg _, cfc_mul] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) (g : ℕ → A) (hg : ∀ n, g n = cfc (fun x : ℂ ↦ x ^ n) a) :
    g 2 * g 3 = cfc (fun x : ℂ ↦ x ^ 2 * x ^ 3) a := by
  cfc_pull? [hg 2, hg _] ℂ a

/- `*` is all the hypotheses, the ones `cfc_pull` can use classified. -/
example (ha : IsStarNormal a) (b : A) (hb : b = a * a) (f : ℂ → ℂ) (hf : star a = cfc f a)
    (hf' : Continuous f) : star a * b = cfc (fun x ↦ f x * (x * x)) a := by
  cfc_pull [*] ℂ a

end Hypotheses

/-! ### Anything else in the list is `simp`'s -/

section Simp

variable {A : Type*} [CStarAlgebra A] {a : A}

def LemmaListTest.cube (a : A) : A := a * a * a

/- A definition to unfold, a rewrite rule, a reversed one. -/
example (ha : IsStarNormal a) (b c : A) (hb : b = a * a) (hc : star a = c) :
    LemmaListTest.cube a + b + c = cfc (fun x : ℂ ↦ x * x * x + x * x + star x) a := by
  cfc_pull [LemmaListTest.cube, hb, ← hc] ℂ a

/--
info: Try this:
  [apply] cfc_pull only [cfc_id', cfc_mul, cfc_add, cfc_star_id, LemmaListTest.cube, hb, ← hc] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) (b c : A) (hb : b = a * a) (hc : star a = c) :
    LemmaListTest.cube a + b + c = cfc (fun x : ℂ ↦ x * x * x + x * x + star x) a := by
  cfc_pull? [LemmaListTest.cube, hb, ← hc] ℂ a

example (ha : IsStarNormal a) (b c : A) (hb : b = a * a) (hc : star a = c) :
    LemmaListTest.cube a + b + c = cfc (fun x : ℂ ↦ x * x * x + x * x + star x) a := by
  cfc_pull only [cfc_id', cfc_mul, cfc_add, cfc_star_id, LemmaListTest.cube, hb, ← hc] ℂ a

end Simp

/-! ### `-lemma` -/

section Erase

variable {A : Type*} [CStarAlgebra A] {a : A}

/- Without both `mul` lemmas the factors are pulled but not the product. -/
/--
error: unsolved goals
A : Type u_1
inst✝ : CStarAlgebra A
a : A
ha : IsStarNormal a
⊢ cfc (fun x ↦ x) a * cfc (fun x ↦ x) a = cfc (fun x ↦ x * x) a
-/
#guard_msgs in
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul, -cfcₙ_mul] ℂ a

/- With `cfc_mul` alone gone, `cfcₙ_mul` and the unitality conversion take over. -/
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul] ℂ a

/--
error: `Nat.add_comm` is not in the `cfc_pull` lemma set, so `-Nat.add_comm` has nothing to remove
-/
#guard_msgs in
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-Nat.add_comm] ℂ a

end Erase

end LemmaList

section Only

/-! ## `only [..]` and `cfc_pull?` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}

open scoped NNReal

/--
info: Try this:
  [apply] cfc_pull only [cfc_star_id, cfc_id', cfc_mul] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull? ℂ a

example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull only [cfc_star_id, cfc_id', cfc_mul] ℂ a

/--
error: unsolved goals
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
⊢ cfc (fun x ↦ star x) a * cfc (fun x ↦ x) a = cfc (fun x ↦ star x * x) a
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull only [cfc_star_id, cfc_id'] ℂ a

/- The suggestion replaces everything up to the element, keeping the configuration and leaving any
location or `=> ..` block as it is; lemmas used at several locations are listed once. -/
/--
info: Try this:
  [apply] cfc_pull +defer only [CFC.rpow_def, cfc_mul] ℝ≥0 a
-/
#guard_msgs in
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull? +defer ℝ≥0 a => all_goals fun_prop

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull +defer only [CFC.rpow_def, cfc_mul] ℝ≥0 a => all_goals fun_prop

/- `at *` visits the hypotheses first, `ha` included, so `cfc_id'` is used before `cfc_star_id`. -/
/--
info: Try this:
  [apply] cfc_pull only [cfc_id', cfc_star_id, cfc_mul] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_pull? ℂ a at *
  exact h

/- A hypothesis in the list is suggested by name. -/
/--
info: Try this:
  [apply] cfc_pull only [hf, cfc_id', cfc_mul] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : star a = cfc f a) (hf' : Continuous f) :
    star a * a = cfc (fun x ↦ f x * x) a := by
  cfc_pull? [hf] ℂ a

/--
info: Try this:
  [apply] cfc_pull only [cfc_star_id, cfc_id', cfc_mul] ℂ a
-/
#guard_msgs in
example (ha : IsStarNormal a) (b : A) : star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a => cfc_pull? ℂ a

end Only

section Only

/-! ## `only [..]` and `cfc_pull?` -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}

open scoped NNReal


example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull [cfc_star_id, cfc_id', cfc_mul] ℂ a


/- The suggestion replaces everything up to the element, keeping the configuration and leaving any
location or `=> ..` block as it is; lemmas used at several locations are listed once. -/

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull +defer [CFC.rpow_def, cfc_mul] ℝ≥0 a => all_goals fun_prop




example (ha : IsStarNormal a) (b : A) : star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a =>
    cfc_pull +defer [cfc_star_id, cfc_id', cfc_mul] ℂ a =>
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
  conv_lhs => cfc_pull ℝ a; cfc_pull ℂ a

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

section AbsNormal

/-! ## `abs` of a merely normal element -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

example (ha : IsStarNormal a) : CFC.abs a * a = cfc (fun x : ℂ ↦ (‖x‖ : ℂ) * x) a := by
  cfc_pull ℂ a

example (ha : IsSelfAdjoint a) : CFC.abs a - a = cfc (fun x : ℝ ↦ ‖x‖ - x) a := by
  cfc_pull ℝ a

example {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {b : B}
    (hb : IsStarNormal b) : CFC.abs b = cfcₙ (fun x : ℂ ↦ (‖x‖ : ℂ)) b := by
  cfc_pull ℂ b

end AbsNormal

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
  cfc_pull ℝ≥0 a => all_goals first | (simp)

/- Over `ℝ` the ordinary `cfc_sub` is preferred, so no such hypothesis appears at all. -/
example (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hg : ContinuousOn g (spectrum ℝ a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull +defer ℝ a => all_goals assumption

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

section Products

/-! ## Pairs -/

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A} {b : B}

/- The components of a pair are targets. `cfc_map_prod`'s hypotheses about the predicate at the
pair and at its components come back as side goals. -/
example (hab : IsStarNormal (a, b)) (ha : IsStarNormal a) (hb : IsStarNormal b) :
    (star a * a, star b * b) = cfc (fun x : ℂ ↦ star x * x) (a, b) := by
  cfc_pull ℂ (a, b)

/- A pair given as a variable is matched up to structure eta. -/
example (c : A × B) (hc : IsStarNormal c) (h₁ : IsStarNormal c.1) (h₂ : IsStarNormal c.2) :
    (star c.1 * c.1, star c.2 * c.2) = cfc (fun x : ℂ ↦ star x * x) c := by
  cfc_pull ℂ c

end Products

section Numerals

/-! ## Numerals -/

variable {A : Type*} [CStarAlgebra A] {a : A}

example (ha : IsStarNormal a) : (2 : A) * a = cfc (fun x : ℂ ↦ 2 * x) a := by cfc_pull ℂ a

example (ha : IsStarNormal a) (n : ℕ) : a + n = cfc (fun x : ℂ ↦ x + n) a := by cfc_pull ℂ a

example (ha : IsSelfAdjoint a) (n : ℤ) : n * a = cfc (fun x : ℝ ↦ n * x) a := by cfc_pull ℝ a

example (ha : IsStarNormal a) : a - 3 = cfc (fun x : ℂ ↦ x - 3) a := by cfc_pull ℂ a

end Numerals

section Regressions

/-! ## Shapes that once failed -/

variable {A : Type*} [CStarAlgebra A] {a : A}

/- `cfc_const` mentions the element only on its calculus side, so it is instantiated at the
target like `cfc_const_one`. -/
example (ha : IsStarNormal a) (z : ℂ) : algebraMap ℂ A z * a = cfc (fun x : ℂ ↦ z * x) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) (z : ℂ) : algebraMap ℂ A z = cfc (fun _ : ℂ ↦ z) a := by
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

/- A side goal raised under a binder is quantified over it; its context is the goal's, not the
binder's. -/
/--
error: unsolved goals
case cfc_pull.continuity
A : Type u_1
inst✝ : CStarAlgebra A
a : A
ha : IsStarNormal a
f : ℕ → ℂ → ℂ
⊢ ∀ (n : ℕ), ContinuousOn (f n) (spectrum ℂ a)

case cfc_pull.continuity
A : Type u_1
inst✝ : CStarAlgebra A
a : A
ha : IsStarNormal a
f : ℕ → ℂ → ℂ
⊢ ∀ (n : ℕ), ContinuousOn (fun x ↦ x) (spectrum ℂ a)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f : ℕ → ℂ → ℂ) :
    ∀ n, cfc (f n) a * a = cfc (fun x ↦ f n x * x) a := by
  cfc_pull +defer ℂ a => skip

/- Flipping the unitality of an argument of a dependent function is not a congruence; the
attempt is skipped rather than failing `simp`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : Continuous f) :
    (⟨cfc f a * a, rfl⟩ : {x : A // x = x}) = ⟨cfc (fun x ↦ f x * x) a, rfl⟩ := by
  cfc_pull ℂ a

/- A hypothesis with the same calculus at the same element on both sides is not a pull. -/
/--
error: `cfc_pull`: both sides of `h` are the same calculus applied to the same element; there is nothing for `cfc_pull` to do with it
-/
#guard_msgs in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) (h : cfc f a = cfc g a) : cfc f a = cfc g a := by
  cfc_pull [h] ℂ a

/- Inside the calculus, an inner element that does not become the calculus applied to something
is left alone: `cfc f (a + b)` does not become `cfc f (cfc id a + b)`. -/
example (ha : IsStarNormal a) (f : ℂ → ℂ) (b : A) :
    cfc f (a + b) * a = cfc f (a + b) * cfc (fun x : ℂ ↦ x) a := by
  cfc_pull ℂ a

end Regressions

section HomOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A}

/- The lemma for the specific homomorphism is preferred to the one for the class. -/
/--
info: Try this:
  [apply] cfc_pull only [StarAlgHom.map_cfc] ℂ (φ a)
-/
#guard_msgs in
example (φ : A →⋆ₐ[ℂ] B) (ha : IsStarNormal a) (hφ : Continuous φ) (f : ℂ → ℂ)
    (hf : Continuous f) : φ (cfc f a) = cfc f (φ a) := by
  cfc_pull? ℂ (φ a)

end HomOrder


/-! # `at` -/

variable {A : Type*} [CStarAlgebra A] {a b : A}


example (ha : IsStarNormal a) (h : star a * a = b) : cfc (fun x : ℂ ↦ star x * x) a = b := by
  cfc_pull ℂ a at h
  exact h

example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_pull ℂ a at h ⊢
  exact h

example (ha : IsStarNormal a) (h : star a * a = a) :
    cfc (fun x : ℂ ↦ star x * x) a = cfc (fun x : ℂ ↦ x) a := by
  cfc_pull ℂ a at h
  exact h

example (ha : IsStarNormal a) (h : star a * a = b) : star a * a = b := by
  cfc_pull ℂ a at *
  exact h

/- Side goals raised at a hypothesis go to the `=> ..` block too. -/
example [PartialOrder A] [StarOrderedRing A] (ha : IsStrictlyPositive a)
    (h : CFC.log a * CFC.log a = b) : cfc (fun x : ℝ ↦ Real.log x * Real.log x) a = b := by
  cfc_pull ℝ a at h =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)
  exact h
