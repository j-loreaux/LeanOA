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

/-!
# Examples for the `cfc_pull` tactic

This is the main test suite for `cfc_pull`. Each example states an identity between an
expression in a C⋆-algebra (or in any algebra with a continuous functional calculus) and the same
expression with `cfc`/`cfcₙ` pulled to the head, and proves it with `cfc_pull`.

`cfc_pull` replaces the goal by an equality of two `cfc` applications — closed by `rfl` when the
two functions agree — and discharges the hypotheses of the lemmas it used with `assumption` and
the standard auto-param tactics `cfc_tac`, `cfc_cont_tac` and `cfc_zero_tac`. Anything it cannot
close is an error unless `+defer` is given, in which case it becomes a goal named after its kind
(`cfc_pull.continuity`, `cfc_pull.predicate`, `cfc_pull.mapZero`, `cfc_pull.side`). `+deferAll`
skips the discharging altogether and hands back every side goal, deduplicated. In `conv` mode,
where a leftover goal cannot escape the block, a trailing `=> tac` block closes them in place.

Examples that `cfc_pull` deliberately does *not* finish are marked as such; in every case what is
left over is either an honest side condition or an equality of functions that has to be settled
with `cfc_congr`.
-/

/- The predicate hypotheses below are used by `cfc_pull` itself (it tries `assumption` on the
side goals it raises), which the unused-variable linter cannot see. -/

section GenericUnital

/- The user supplies the scalar ring `R` and the element `a`; the unital calculus is used because
the algebra has one. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

/- Both arguments are required and positional: the element `a` fixes the algebra, and so the
subterms of the goal to act on, and the scalar ring `R` fixes the calculus. Neither is read off
the goal. -/
example (ha : p a) :
    star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a

/- Note that `+defer` would make no difference here: it does not switch the discharging off, it
only changes what happens to the goals the discharging could not close, and here there are none.
See the `MessySideGoals` section below for where it does matter. -/

example (ha : p a) (hf : ContinuousOn f (spectrum R a)) (hg : ContinuousOn g (spectrum R a)) :
    star (cfc f a) + cfc g a + a = cfc (fun x ↦ star (f x) + g x + x) a := by
  cfc_pull R a

example (ha : p a) :
    a ^ 2 + 3 • a * cfc (id : R → R) a = cfc (fun x : R ↦ x ^ 2 + 3 • x * x) a := by
  cfc_pull R a

/- Composition: the calculus is applied to `a ^ 2` rather than to `a`, which `cfc_comp_pow`
resolves in one step. -/
example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' spectrum R a)) :
    cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a := by
  cfc_pull R a

/- A double composition: `cfc_comp_pow` peels off the power, and `cfc_comp'` the inner `cfc`. -/
example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  cfc_pull R a

/- `cfc_pull` also works in `conv` mode, which is how one pulls at a specific position. -/
example (ha : p a) (b : A) :
    star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv in star a * a => cfc_pull R a

/- `cfc_pull` does not go under binders; `conv` does. Pull each summand under the binder first,
and then let `cfc_sum` collect the result. -/
example {ι : Type*} {s : Finset ι} {h : ι → R → R}
    (hh : ∀ i, ContinuousOn (h i) (spectrum R a)) :
    ∑ i ∈ s, star (cfc (h i) a) = cfc (∑ i ∈ s, fun x ↦ star (h i x)) a := by
  conv_lhs => enter [2, i]; cfc_pull R a
  cfc_pull R a

/- The hypothesis `cfc_sum` asks for is `∀ i ∈ s, ContinuousOn (h i) (spectrum R a)`: a
continuity goal wrapped in a binder. It is classified as one all the same — the classification
looks for `Continuous`/`ContinuousOn` anywhere in the statement, not just at its head — so it is
named `cfc_pull.continuity`, and `cfc_cont_tac` is what closed it above. -/
example {ι : Type*} {s : Finset ι} {h : ι → R → R}
    (hh : ∀ i, ContinuousOn (h i) (spectrum R a)) :
    ∑ i ∈ s, star (cfc (h i) a) = cfc (∑ i ∈ s, fun x ↦ star (h i x)) a := by
  conv_lhs => enter [2, i]; cfc_pull R a
  cfc_pull +deferAll R a
  case cfc_pull.continuity => exact fun i _ ↦ (hh i).star

end GenericUnital

section GenericNonUnital

/- Here the algebra is not unital, so `cfc_pull` falls back to `cfcₙ` without being told to. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
  {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  cfc_pull R a

example (ha : p a) (hf : ContinuousOn f (quasispectrum R a)) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    star (cfcₙ f a) + cfcₙ g a + a = cfcₙ (fun x ↦ star (f x) + g x + x) a := by
  cfc_pull R a

example (ha : p a) :
    a * a + 3 • a * cfcₙ (id : R → R) a = cfcₙ (fun x : R ↦ x * x + 3 • x * x) a := by
  cfc_pull R a

/- Note that `cfc_pull` produces `f (x * x)`, not `f (x ^ 2)`: it follows the shape of the term
it is given, and there is no `cfcₙ_pow` to turn `a * a` into a square. -/
example (ha : p a) (hf : ContinuousOn f ((fun x : R ↦ x * x) '' quasispectrum R a))
    (hf0 : f 0 = 0) :
    cfcₙ f (a * a) = cfcₙ (fun x ↦ f (x * x)) a := by
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

example (ha : IsStarNormal a) :
    NormedSpace.exp (I • a) = cfc (fun x ↦ Complex.exp (I • x)) a := by
  cfc_pull ℂ a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a = cfc Real.exp a := by
  cfc_pull ℝ a

example : CFC.sqrt a = cfcₙ NNReal.sqrt a := by
  cfc_pull ℝ≥0 a

/- Over `ℝ`, `CFC.sqrt` is pulled with `CFC.sqrt_eq_real_sqrt` rather than by converting the
`ℝ≥0` calculus, which is why the function comes out as `Real.sqrt`. -/
example (ha : 0 ≤ a) :
    1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by
  cfc_pull ℝ a

/- Here `f` is arbitrary, so its continuity is a genuine side goal. -/
example (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (CFC.sqrt (a ^ 2)))) :
    CFC.sqrt (CFC.sqrt (a ^ 2)) + cfcₙ f (CFC.sqrt (a ^ 2)) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (CFC.sqrt (a ^ 2)) := by
  cfc_pull -unital ℝ≥0 (CFC.sqrt (a ^ 2))

/- Pulling over `ℂ` a term whose natural home is the non-unital calculus over `ℝ`: `cfc_pull`
uses `CFC.posPart_def`, then `cfcₙ_eq_cfc`, then `cfc_real_eq_complex`. -/
example (ha : IsSelfAdjoint a) :
    a⁺ = cfc (fun z : ℂ ↦ (z.re⁺ : ℝ)) a := by
  cfc_pull ℂ a

/- `a⁺`/`a⁻`, keeping the non-unital `cfcₙ` head even in a unital algebra. -/
example : a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull -unital ℝ a

example : a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  cfc_pull -unital ℝ a

/- Mixing the (non-unital) `a⁺` with the unital constant `1` forces a `cfc` head. -/
example (ha : IsSelfAdjoint a) :
    1 - a⁺ = cfc (fun x : ℝ ↦ 1 - x⁺) a := by
  cfc_pull ℝ a

/- `CFC.abs`, pulled over its own scalar ring `ℝ≥0` at the base point `star a * a`. -/
example (a : A) :
    CFC.abs a * CFC.abs a = cfcₙ (fun x : ℝ≥0 ↦ NNReal.sqrt x * NNReal.sqrt x) (star a * a) := by
  cfc_pull ℝ≥0 (star a * a)

/- `a ^ (x : ℝ)`, pulled over `ℝ≥0`. `CFC.rpow_def` is definitional, so there is nothing to
discharge here; the product below does need continuity, which `fun_prop` gets from `0 ≤ x`. -/
example (a : A) (x : ℝ) :
    a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x) a := by
  cfc_pull ℝ≥0 a

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull ℝ≥0 a

example : CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  cfc_pull ℝ≥0 a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp x * Real.exp x) a := by
  cfc_pull ℝ a

example (ha : IsStarNormal a) (z : ℂ) :
    NormedSpace.exp (z • a) = cfc (fun w : ℂ ↦ Complex.exp (z * w)) a := by
  cfc_pull ℂ a

/- `CFC.log` composed with `NormedSpace.exp`, pulled (not simplified away) into a single `cfc`. -/
example (ha : IsSelfAdjoint a) :
    CFC.log (NormedSpace.exp a) = cfc (fun x : ℝ ↦ Real.log (Real.exp x)) a := by
  cfc_pull ℝ a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp (-a) * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp (-x) * Real.exp x) a := by
  cfc_pull ℝ a

/- Inversion in `Aˣ`, using the unital `cfc`. -/
example (u : Aˣ) (ha : IsStarNormal (u : A)) :
    (↑u⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (u : A) := by
  cfc_pull ℂ (u : A)

example (f g : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ a)) (hg : ContinuousOn g (spectrum ℂ a)) :
    cfc f a * cfc g a = cfc (fun z ↦ f z * g z) a := by
  cfc_pull ℂ a

end CStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open Complex
open scoped NNReal

example :
    a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull ℝ a

example :
    a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  cfc_pull ℝ a

example (a : A) :
    CFC.abs a = cfcₙ NNReal.sqrt (star a * a) := by
  cfc_pull ℝ≥0 (star a * a)

example : CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  cfc_pull ℝ≥0 a

/- The element is `star a * a`, not `a` itself. -/
example (a : A) (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (star a * a))) :
    CFC.sqrt (star a * a) + cfcₙ f (star a * a) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (star a * a) := by
  cfc_pull ℝ≥0 (star a * a)

example (f g : ℂ → ℂ) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℂ a)) (hg : ContinuousOn g (quasispectrum ℂ a)) :
    cfcₙ f a * cfcₙ g a = cfcₙ (fun z ↦ f z * g z) a := by
  cfc_pull ℂ a

/- The predicate `IsSelfAdjoint a` is genuinely needed here and is left to the user. -/
example (ha : IsSelfAdjoint a) :
    (-a)⁺ = cfcₙ (fun x : ℝ ↦ (-x)⁺) a := by
  cfc_pull ℝ a

example (y : ℝ≥0) (hy : y ≠ 0) :
    CFC.sqrt a * a ^ y = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.nnrpow t y) a := by
  cfc_pull ℝ≥0 a

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : ContinuousOn f ((fun x : ℝ ↦ x⁺) '' quasispectrum ℝ a)) :
    cfcₙ f a⁺ = cfcₙ (fun x ↦ f (x⁺)) a := by
  cfc_pull ℝ a

example (ha : IsSelfAdjoint a) :
    (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by
  cfc_pull ℝ a

example (ha : IsStarNormal a) (z : ℂ) :
    z • star a = cfcₙ (fun w : ℂ ↦ z * star w) a := by
  cfc_pull ℂ a

end NonUnitalCStarAlgebra

section MessySideGoals

/-! ## Side goals the auto-param tactics cannot close

`cfc_tac`, `cfc_cont_tac` and `cfc_zero_tac` between them handle continuity of everything
`fun_prop` knows and the routine predicate goals. Plenty of side goals are outside that reach:
continuity on a set that has to be located first, or a hypothesis about the values a function
takes on the spectrum. Those are an error by default, and `+defer` hands them back — named, so
that `case cfc_pull.continuity => ..` picks them out. `cfc_pull` has already done the structural
half of the work. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open scoped NNReal

/- `Real.log` is not continuous at `0`, so `cfc_mul` leaves a continuity goal that `fun_prop`
cannot discharge. It follows from `IsStrictlyPositive a`, but only after unfolding that to
`IsUnit a` and going through `spectrum.zero_notMem`. Note that the goal appears once, not twice,
even though `cfc_mul` asks for it on both factors: identical side goals are merged. -/
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +defer ℝ a
  case cfc_pull.continuity =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/- The same story one ring down: `(· ^ x)` on `ℝ≥0` is continuous away from `0` when `x < 0`. -/
example (ha : IsStrictlyPositive a) (x : ℝ) :
    a ^ x * a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ x) a := by
  cfc_pull +defer ℝ≥0 a
  case cfc_pull.continuity =>
    exact NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem ℝ≥0 ha.2))

/- Not every side goal is a continuity goal: `cfc_inv` needs the function to be nonvanishing on
the spectrum, which here takes a hypothesis about the spectrum's location. -/
example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull +deferAll ℝ a
  case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
  case cfc_pull.predicate => exact ha
  case cfc_pull.continuity => fun_prop

end MessySideGoals

section DeferAll

/-! ## `+deferAll`: every side goal, discharged by hand

`+defer` returns only the goals the discharging could not close, so what comes back depends on
how far `fun_prop` and `cfc_tac` happened to get. `+deferAll` switches the discharging off
instead — no `assumption`, no auto-param tactic, no `(disch := ..)` — so the goal list is exactly
the hypotheses of the lemmas the pull used. Deduplication still runs first, and that is what
makes `cfc_pull +deferAll .. <;> tac` a sensible thing to write. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A}

/- Plain `cfc_pull R a` closes this outright (it is the first example in the file). With
`+deferAll` the three hypotheses it would have used come back instead: the shared predicate
goal `p a`, asked for by `cfc_star_id` and by `cfc_id'`, and the two continuity hypotheses of
`cfc_mul`. -/
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull +deferAll R a <;> first | assumption | fun_prop

/- The goals are named after their kind, exactly as with `+defer`. -/
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull +deferAll R a
  case cfc_pull.predicate => exact ha
  all_goals fun_prop

end DeferAll

section DeferAllCStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

/- Deduplication is what keeps the list short: `cfc_mul` asks for the continuity of `Real.log`
once per factor, and one goal comes back, not two. Compare the `+defer` version of this example
in `MessySideGoals` above — there the deduplication is invisible, because the auto-param tactic
had already failed on both copies. -/
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +deferAll ℝ a
  exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/- `(disch := ..)` is inert under `+deferAll`: nothing at all is run on a side goal, the
discharger included. This is the `cfc_pull.side` example from `MessySideGoals` above, where the
discharger does close the goal when `+deferAll` is absent; here the same discharger is given and
the goal still comes back, so the `case cfc_pull.side` below is what proves it. -/
example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f)
    (hspec : spectrum ℝ a ⊆ Set.Icc (-1) 1) (hf0 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ≠ 0) :
    Ring.inverse (cfc f a) = cfc (fun x : ℝ ↦ (f x)⁻¹) a := by
  cfc_pull +deferAll (disch := exact fun x hx ↦ hf0 x (hspec hx)) ℝ a
  case cfc_pull.side => exact fun x hx ↦ hf0 x (hspec hx)
  case cfc_pull.predicate => exact ha
  case cfc_pull.continuity => fun_prop

end DeferAllCStar

section ConvSideGoals

/-! ## `=> tac`: side goals inside a `conv` block

A `conv` block cannot end with unsolved goals, so in `conv` mode a side goal that survives the
discharging is fatal, and `+defer`/`+deferAll` — which only move goals onto the goal list — are
no help at all. The `=> tac` block is the way out, and is to `conv` mode what the tactic
following `cfc_pull +defer ..` is to tactic mode: the surviving side goals become its goal list,
the `conv` goal is set aside so the block cannot touch it, and the block has to close all of
them. Writing the block implies `+defer`. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

/- The motivating case. `Real.log` is continuous only away from `0`, so `cfc_cont_tac` cannot
close the continuity goal, and without the block this `conv` cannot be closed at all. -/
example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_pull ℝ a =>
      exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/- The goals keep their kind tags inside the block, so `case` addresses a group here exactly as
it does in tactic mode. -/
example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_pull ℝ a =>
      case cfc_pull.continuity =>
        exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/- `+deferAll .. => all_goals tac` is the `conv`-mode counterpart of the tactic-mode idiom
`cfc_pull +deferAll .. <;> tac`: the block faces the hypotheses of the lemmas the pull used,
rather than whatever the auto-param tactics happened to leave. This pull needs no block at all
without `+deferAll` — the discharging closes all three goals — which is what makes it the honest
illustration of what the flag hands over. -/
example (ha : IsStarNormal a) (b : A) :
    star a * a + b = cfc (fun x : ℂ ↦ star x * x) a + b := by
  conv in star a * a =>
    cfc_pull +deferAll ℂ a =>
      case cfc_pull.predicate => exact ha
      all_goals fun_prop

/- The block is a tactic sequence and so is delimited by indentation: the `conv` step after it
belongs to the enclosing `conv` block and is not swallowed. Unlike `equals`, the block does not
have to come last. -/
example (ha : IsStrictlyPositive a) (b : A) :
    CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv_lhs =>
    enter [1]
    cfc_pull ℝ a =>
      exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)
    rfl

end ConvSideGoals

section LetBound

/-! ## `let`-bound variables and `+zetaDelta`

A local definition is an atom: `cfc_pull` does not look at what it stands for. The default is
`false` for the reason `simp` chose the same one — `set b := e with hb` is a request to stop
reading `e`, and unfolding it silently would undo the abstraction and strand `hb`. -/

variable {A : Type*} [CStarAlgebra A] {a : A}

/- With `+zetaDelta` the definition is unfolded and the pull proceeds on its structure. -/
example (ha : IsStarNormal a) : True := by
  let b : A := star a * a
  have : b = cfc (fun x : ℂ ↦ star x * x) a := by
    cfc_pull +zetaDelta ℂ a
  trivial

/- Transitively, through nested definitions. -/
example (ha : IsStarNormal a) : True := by
  let u : A := star a
  let v : A := u * a
  have : v = cfc (fun x : ℂ ↦ star x * x) a := by
    cfc_pull +zetaDelta ℂ a
  trivial

/- The other way in, and the reason the default is what it is: `set` hands you the equation, so
you decide when the abstraction is opened rather than the tactic deciding for you. -/
example (ha : IsStarNormal a) : True := by
  have : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
    set b := star a * a with hb
    rw [hb]
    cfc_pull ℂ a
  trivial

/- The *element* is a separate question and needs no flag: it is matched against the term the
user supplied, so a `let`-bound element is matched as written and comes back as written — note
the `c` rather than `a` on the right. -/
example (ha : IsStarNormal a) : True := by
  let c : A := a
  have hc : IsStarNormal c := ha
  have : star c * c = cfc (fun x : ℂ ↦ star x * x) c := by
    cfc_pull ℂ c
  trivial

end LetBound

section LemmaList

/-! ## `[..]`: the lemma set for one call

The lemmas `cfc_pull` uses are those tagged `@[cfc_pull]`. A bracketed list — before the scalar
ring and the element, where `simp`'s and `rw`'s lists go relative to their location — adjusts
that set for a single call: `foo` adds a lemma and `-foo` takes one out. The database itself is
never modified, which is the point — a lemma that would be a nuisance tagged globally is still
usable where it is wanted. See the `CFC.sqrt` example in `InTheWild` below for the case this was
built for. -/

namespace LemmaListTest

variable {A : Type*} [CStarAlgebra A] {a : A}

/- `public` only so that the error message below names `LemmaListTest.sq` rather than the
private-name mangling of it; this file has no `public section`. The head symbol is reported
fully qualified, while the expression beside it is printed as it would be written here. -/

/-- An operation the `@[cfc_pull]` set says nothing about … -/
public def sq (a : A) : A := a * a

/-- … and the lemma that reads it, deliberately left untagged. -/
public theorem cfc_sq (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    sq (cfc f a) = cfc (fun x ↦ f x * f x) a :=
  (cfc_mul f f a hf hf).symm

/- Without it the pull stops at `sq a`, which is an atom as far as the tactic is concerned. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `sq a`
    (head symbol: LemmaListTest.sq, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull ℂ a

/- Naming it is all it takes; it is classified exactly as the attribute would classify it. -/
example (ha : IsStarNormal a) : sq a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [cfc_sq] ℂ a

/- A listed lemma's own hypotheses are classified like any other side goal, and by *shape*:
`cfc_zero_tac` exists for the `f 0 = 0` hypothesis of the non-unital calculus, so only an
equation whose right-hand side is zero is named `cfc_pull.mapZero`. Any other equation — here
`f 1 = 1` — is a hypothesis peculiar to the lemma, and comes back as `cfc_pull.side`, where
`(disch := ..)` can reach it. -/
/-- A variant of `cfc_sq` with an equational hypothesis that is not `f 0 = 0`. -/
public theorem cfc_sq_of_map_one (f : ℂ → ℂ) (a : A) (_hf1 : f 1 = 1)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    sq (cfc f a) = cfc (fun x ↦ f x * f x) a :=
  (cfc_mul f f a hf hf).symm

example (_ha : IsStarNormal a) (f : ℂ → ℂ) (hf : Continuous f) (hf1 : f 1 = 1) :
    sq (cfc f a) = cfc (fun x : ℂ ↦ f x * f x) a := by
  cfc_pull +deferAll [cfc_sq_of_map_one] ℂ a
  case cfc_pull.side => exact hf1
  all_goals first | assumption | fun_prop

/- There is no right-to-left form, here or on the attribute: the equation is recognised from
whichever side carries the calculus and applied in whichever direction the pull calls for, so
`cfc_sq` would do the same work stated the other way round. The one category where the
direction matters is `Scalar`, and there the direction the lemma is stated in is the direction
of the conversion. -/

/- And in `conv` mode, where it goes before the `=> ..` block. -/
example (ha : IsStarNormal a) (b : A) : sq a + b = cfc (fun x : ℂ ↦ x * x) a + b := by
  conv in sq a =>
    cfc_pull +deferAll [cfc_sq] ℂ a =>
      case cfc_pull.predicate => exact ha
      all_goals fun_prop

/- `-foo` takes a lemma out. `a * a` is read by `cfc_mul`, or failing that by `cfcₙ_mul` followed
by a conversion to the unital calculus; with both gone there is nothing left that can read it. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `a * a`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul, -cfcₙ_mul] ℂ a

/- Removing one of the two leaves the other to do the work, so the goal still closes — see
`Tracing.lean` for the trace that shows the difference. -/
example (ha : IsStarNormal a) : a * a = cfc (fun x : ℂ ↦ x * x) a := by
  cfc_pull [-cfc_mul] ℂ a

end LemmaListTest

end LemmaList

section RealTheorems

/-! ## `cfc_pull` followed by `cfc_congr`

This is the workflow the tactic exists for. `cfc_pull` reduces an identity between two
expressions built from the calculus to an identity between the two functions, and `cfc_congr`
then reduces that to a pointwise statement on the spectrum. Neither of the two functions below is
the one the user wrote down; that is exactly the point. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open scoped NNReal

example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = a := by
  cfc_pull ℝ≥0 a
  exact cfc_congr fun x _ ↦ NNReal.mul_self_sqrt x

example (ha : IsSelfAdjoint a) : CFC.log (NormedSpace.exp a) = a := by
  cfc_pull ℝ a
  exact cfc_congr fun x _ ↦ Real.log_exp x

example (ha : IsSelfAdjoint a) : a⁺ - a⁻ = a := by
  cfc_pull ℝ a
  exact cfc_congr fun x _ ↦ by simp

end RealTheorems

section InTheWild

/- Goals of this shape have appeared in Mathlib. -/

open Complex
open scoped NNReal CStarAlgebra

section NonUnital

variable {A : Type*} [CStarAlgebra A] {a : A}

example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℝ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull ℝ (star a * a : A⁺¹)

example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℂ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull ℂ (star a * a : A⁺¹)

-- this is a bit of a weird example because it pulls towards `ℝ` rather than `ℂ`.
example : ((star a * a) * (1 - star a * a) ^ 2 : A⁺¹) =
    cfc (fun x : ℂ => x * (1 - x) ^ 2) (star a * a : A⁺¹) := by
  cfc_pull +defer ℝ (star a * a : A⁺¹)
  case cfc_pull.side =>
    rw [← IsSelfAdjoint.spectrumRestricts (by cfc_tac) |>.algebraMap_image]
    simp
  norm_cast

end NonUnital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

/- `CFC.sqrt_eq_cfc_complex_sqrt` and its non-unital counterpart
`CFC.sqrt_eq_cfcₙ_complex_sqrt` are deliberately *not* tagged `@[cfc_pull]`: `Complex.sqrt` is
continuous only away from the negative reals, so tagging them would put a `ContinuousOn
Complex.sqrt ..` goal in the way of every pull that meets a square root — one that can be closed
only when the element is known to be nonnegative. Naming the lemma where it is wanted costs
nothing. -/
example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_pull [CFC.sqrt_eq_cfc_complex_sqrt] ℂ a

/- The non-unital lemma reaches the same goal through `cfcₙ_eq_cfc`, at the cost of the
`Complex.sqrt 0 = 0` side goal that conversion raises. -/
example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_pull [CFC.sqrt_eq_cfcₙ_complex_sqrt] ℂ a

example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a

/- `cfc_pull` converts from the non-unital calculus over `ℝ` to the unital one over `ℂ`. It does
not close the goal: it produces `fun x ↦ x + I * ↑√(1 - x.re ^ 2)`, whereas the statement asks
for `fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)`. Both are correct — `a` is selfadjoint, so the two
functions agree on `spectrum ℂ a` — and closing the gap is exactly the job of `cfc_congr`. -/
example (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

/- The same, but starting from `CFC.sqrt (1 - a ^ 2)`. `cfc_pull` uses `CFC.sqrt_eq_real_sqrt`,
whose hypothesis `0 ≤ 1 - a ^ 2` becomes a side goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull +defer ℂ a
  · refine cfc_congr fun x hx ↦ ?_
    rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]
  · -- the side goal `0 ≤ 1 - a ^ 2` left by `CFC.sqrt_eq_real_sqrt`
    have key : (1 : A) - a ^ 2 = cfc (fun x : ℝ ↦ 1 - x ^ 2) a := by cfc_pull ℝ a
    rw [key]
    refine cfc_nonneg fun x hx ↦ ?_
    have hx' : |x| ≤ 1 := by
      simpa [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans ha_norm
    nlinarith [sq_abs x, abs_le.mp hx']

end InTheWild

section RealImaginaryPart

/-! ## The real and imaginary parts

`cfc_re_id` and `cfc_im_id` are `Pull` lemmas: they turn `ℜ a` and `ℑ a` into applications of the
calculus over `ℂ`. `cfc_realPart` and `cfc_imaginaryPart` are `Compose` lemmas: a calculus
already applied at `ℜ a` is rewritten into one at `a`. -/

variable {A : Type*} [CStarAlgebra A] {a : A}

open Complex ComplexStarModule

example (ha : IsStarNormal a) : (ℜ a : A) = cfc (fun x : ℂ ↦ (x.re : ℂ)) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) : (ℑ a : A) = cfc (fun x : ℂ ↦ (x.im : ℂ)) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) :
    star (ℜ a : A) * (ℑ a : A) = cfc (fun x : ℂ ↦ star (x.re : ℂ) * (x.im : ℂ)) a := by
  cfc_pull ℂ a

example (ha : IsStarNormal a) :
    (ℜ a : A) + I • (ℑ a : A) = cfc (fun x : ℂ ↦ (x.re : ℂ) + I * (x.im : ℂ)) a := by
  cfc_pull ℂ a

/- `cfc_realPart` as a composition: the element `ℜ a` is made simpler. -/
example (f : ℂ → ℂ) (ha : IsStarNormal a) (hf : ContinuousOn f (spectrum ℂ (ℜ a : A))) :
    cfc f (ℜ a : A) = cfc (fun x : ℂ ↦ f x.re) a := by
  cfc_pull ℂ a

example (f : ℂ → ℂ) (ha : IsStarNormal a) (hf : ContinuousOn f (spectrum ℂ (ℑ a : A))) :
    star (cfc f (ℑ a : A)) = cfc (fun x : ℂ ↦ star (f x.im)) a := by
  cfc_pull ℂ a

end RealImaginaryPart

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

section HermitianMatrix

/-! ## Hermitian matrices

`Matrix.IsHermitian.cfc_eq` turns the bespoke spectral-theorem construction into the generic
calculus, which is the direction the library recommends. -/

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {M : Matrix n n 𝕜}

example (hM : M.IsHermitian) (f : ℝ → ℝ) : hM.cfc f = cfc f M := by
  cfc_pull ℝ M

example (hM : M.IsHermitian) (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ M))
    (hg : ContinuousOn g (spectrum ℝ M)) :
    hM.cfc f * hM.cfc g = cfc (fun x ↦ f x * g x) M := by
  cfc_pull ℝ M

-- NB: LeanOA sets `backward.isDefEq.respectTransparency false` package-wide as a temporary
-- workaround; under it `cfc_star` fails to match `star (hM.cfc f)` and the pull falls through to
-- the non-unital calculus. Restore the stock setting, which is what mathlib will run this under.
set_option backward.isDefEq.respectTransparency true in
example (hM : M.IsHermitian) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ M)) :
    star (hM.cfc f) - M = cfc (fun x ↦ star (f x) - x) M := by
  cfc_pull ℝ M

end HermitianMatrix

section AbsNorm

/-! ## `cfc_comp_norm`

A composition lemma whose structured element is `CFC.abs a`. -/

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

/-! ## Truncated subtraction over `ℝ≥0`

`cfc_sub` needs a `CommRing`, so over `ℝ≥0` it is rejected by instance synthesis and `cfc_tsub`
takes over. It carries the extra hypothesis `∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x`, which becomes a
`cfc_pull.side` goal. `cfc_tsub` is tagged at a lower priority, so over a ring `cfc_sub` still
wins. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open scoped NNReal

example (f g : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x)
    (hf : ContinuousOn f (spectrum ℝ≥0 a)) (hg : ContinuousOn g (spectrum ℝ≥0 a)) :
    cfc f a - cfc g a = cfc (fun x ↦ f x - g x) a := by
  cfc_pull ℝ≥0 a

/- With a concrete `f` and `g` the extra hypothesis is closed automatically. -/
example (ha : 0 ≤ a) :
    cfc (fun x : ℝ≥0 ↦ x + 1) a - a = cfc (fun x : ℝ≥0 ↦ x + 1 - x) a := by
  cfc_pull ℝ≥0 a

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

/-! ## Star algebra homomorphisms

`StarAlgHom.map_cfc` pulls `φ (cfc f a)` towards the calculus at `φ a`. Note that the element to
pull towards is `φ a`, in the *codomain*: `cfc_pull` fixes one algebra and one element for the
whole run, so it cannot descend through `φ` into `A`. -/

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A}

example (φ : A →⋆ₐ[ℂ] B) (f : ℂ → ℂ) (hφ : Continuous φ) (ha : IsStarNormal a)
    (hφa : IsStarNormal (φ a)) (hf : ContinuousOn f (spectrum ℂ a)) :
    φ (cfc f a) = cfc f (φ a) := by
  cfc_pull ℂ (φ a)

example (φ : A →⋆ₐ[ℂ] B) (f g : ℂ → ℂ) (hφ : Continuous φ) (ha : IsStarNormal a)
    (hφa : IsStarNormal (φ a)) (hf : ContinuousOn f (spectrum ℂ a))
    (hg : ContinuousOn g (spectrum ℂ a))
    (hf' : ContinuousOn (fun x ↦ star (f x)) (spectrum ℂ (φ a)))
    (hg' : ContinuousOn g (spectrum ℂ (φ a))) :
    star (φ (cfc f a)) * φ (cfc g a) = cfc (fun x ↦ star (f x) * g x) (φ a) := by
  cfc_pull ℂ (φ a)

end StarAlgHom

section NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] {a : A}

example (φ : A →⋆ₙₐ[ℂ] B) (f : ℂ → ℂ) (hφ : Continuous φ) (ha : IsStarNormal a) (hf₀ : f 0 = 0)
    (hφa : IsStarNormal (φ a)) (hf : ContinuousOn f (quasispectrum ℂ a)) :
    φ (cfcₙ f a) = cfcₙ f (φ a) := by
  cfc_pull ℂ (φ a)

end NonUnitalStarAlgHom

section Unitization

/-! ## The unitization

`Unitization.complex_cfcₙ_eq_cfc_inr` and friends pull `↑(cfcₙ f a)` into the unital calculus at
`↑a`. As with `StarAlgHom.map_cfc`, the pull happens entirely inside `A⁺¹`: `cfc_pull` cannot
descend through the coercion into `A`. -/

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

open scoped NNReal

example (f : ℂ → ℂ) (hf₀ : f 0 = 0) (ha : IsStarNormal (a : Unitization ℂ A))
    (hf : ContinuousOn f (spectrum ℂ (a : Unitization ℂ A))) :
    (1 : Unitization ℂ A) - ((cfcₙ f a : A) : Unitization ℂ A) =
      cfc (fun x : ℂ ↦ 1 - f x) (a : Unitization ℂ A) := by
  cfc_pull ℂ (a : Unitization ℂ A)

example (f : ℝ → ℝ) (hf₀ : f 0 = 0) :
    ((cfcₙ f a : A) : Unitization ℂ A) = cfc f (a : Unitization ℂ A) := by
  cfc_pull ℝ (a : Unitization ℂ A)

end Unitization
