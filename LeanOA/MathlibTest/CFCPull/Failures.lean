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
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Failure modes of `cfc_pull`

Every way `cfc_pull` and its attribute can fail, pinned down with `#guard_msgs`. This is partly
regression testing and partly documentation: these messages are what a user sees when something
goes wrong, so it is worth keeping them legible.
-/

@[expose] public section

open scoped NNReal

section Tactic

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}

/-! ### Failures in the tactic -/

/--
error: `cfc_pull` found nothing of type `A` in the goal
  2 = 2
-/
#guard_msgs in
example (ha : IsStarNormal a) : (2 : ℕ) = 2 := by
  cfc_pull ℂ a

/--
error: `cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from
which to read off the scalar ring and the element; supply them explicitly, as in
`cfc_pull ℝ a`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull

/--
error: `cfc_pull`'s first argument is the scalar ring, but `a` did not elaborate as a type:
  type expected, got
    (a : A)
If `a` is the element to pull towards, give the scalar ring too — or `_`, as in `cfc_pull _ a`.
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull a

/- Which is exactly what `_` is for: the element alone, with the ring read off the goal. -/
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull _ a

/--
error: `cfc_pull` made no progress
  `cfc_pull`: `A` has no non-unital continuous functional calculus over `ℚ`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull ℚ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `f a`
    (head symbol: _, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f : A → A) : f a = f a := by
  cfc_pull ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `star b * b`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : star b * b = star b * b := by
  cfc_pull ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` reached its maximum recursion depth of 1; either
  the expression is more deeply nested than that, or the `@[cfc_pull]` lemma set is
  looping. Raise the limit with `cfc_pull (maxDepth := 2) ..`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull (maxDepth := 1) ℂ a

/- Not every failure is a failure to rewrite. Reaching `ℝ≥0` from `ℝ` is a scalar conversion
with a side condition of its own — `cfc_real_eq_nnreal` asks for `0 ≤ a` — so a pull towards
`ℝ≥0` of an element that is only known to be selfadjoint gets all the way there and then fails
on the condition. -/
/--
error: `cfc_pull` rewrote the goal but could not discharge 1 side goal:
  case cfc_pull.side
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsSelfAdjoint a
  ⊢ 0 ≤ a
Use `cfc_pull +defer ..` to have them added to the goal list instead.
-/
#guard_msgs in
example (ha : IsSelfAdjoint a) : a⁺ = a⁺ := by
  cfc_pull ℝ≥0 a

/- Side goals that neither `assumption` nor the auto-param tactics can close are an error unless
`+defer` is given. -/
/--
error: `cfc_pull` rewrote the goal but could not discharge 2 side goals:
  case cfc_pull.continuity
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsStarNormal a
  f g : ℂ → ℂ
  ⊢ ContinuousOn f (spectrum ℂ a)

  case cfc_pull.continuity
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsStarNormal a
  f g : ℂ → ℂ
  ⊢ ContinuousOn g (spectrum ℂ a)
Use `cfc_pull +defer ..` to have them added to the goal list instead.
-/
#guard_msgs (whitespace := lax) in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) :
    cfc f a * cfc g a = cfc (fun x ↦ f x * g x) a := by
  cfc_pull ℂ a

/- `+defer` does not help inside `conv`, which cannot end with unsolved goals — the same
restriction that `rw` inside `conv` is subject to. A `=> tac` block is what closes them there;
see the `ConvSideGoals` section of `Examples.lean`. -/
/--
error: Tactic `conv` failed: There are unsolved goals
case cfc_pull.continuity
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
f g : ℂ → ℂ
⊢ ContinuousOn f (spectrum ℂ a)

case cfc_pull.continuity
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
f g : ℂ → ℂ
⊢ ContinuousOn g (spectrum ℂ a)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) :
    cfc f a * cfc g a + b = cfc (fun x ↦ f x * g x) a + b := by
  conv_lhs => arg 1; cfc_pull +defer ℂ a

/- `+deferAll` makes `conv` strictly worse *on its own*: it hands back the side goals that the
discharging would have closed, so a `conv` pull that succeeds without it fails with it. It is
useful there only together with a `=> tac` block, which is then handed the whole list. -/
/--
error: Tactic `conv` failed: There are unsolved goals
case cfc_pull.predicate
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
⊢ IsStarNormal a
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a + b = cfc (fun x : ℂ ↦ star x) a + b := by
  conv_lhs => arg 1; cfc_pull +deferAll ℂ a

/- Nor does `+deferAll` turn a failed pull into a list of goals: it only changes what becomes of
the side goals of a pull that succeeded. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `star b * b`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : star b * b = star b * b := by
  cfc_pull +deferAll ℂ a

/- A `=> tac` block that does not close everything it was handed is an error naming what is
left, rather than the bare `conv` complaint the same goal would have produced without a block.
Note also what reaches the block: `hf` settles `f`'s continuity during the discharging, so only
`g`'s is left for it — the block implies `+defer`, not `+deferAll`. -/
/--
error: `cfc_pull` ran the `=> ..` block, but 1 side goal is still open:
  case cfc_pull.continuity
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsStarNormal a
  f g : ℂ → ℂ
  hf : ContinuousOn f (spectrum ℂ a)
  ⊢ ContinuousOn g (spectrum ℂ a)
A `conv` block cannot end with unsolved goals, so the `=> ..` block must close every one.
-/
#guard_msgs in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc f a * cfc g a + b = cfc (fun x ↦ f x * g x) a + b := by
  conv_lhs => arg 1; cfc_pull ℂ a => skip

/- A local definition is an atom by default, so the pull stops at one. The head symbol is `_`,
as it is for any free variable, so the message names `+zetaDelta` rather than leaving the user
with nothing to go on. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `d`
    (head symbol: _, target: cfc over ℂ at `a`)
  `d` is a local definition, and `cfc_pull` does not look
  at what it stands for. Unfold it with `cfc_pull +zetaDelta ..`, or rewrite it away
  first — `set .. with h` hands you the equation `h` to do it with.
-/
#guard_msgs in
example (ha : IsStarNormal a) : True := by
  let d : A := star a * a
  have : d = cfc (fun x : ℂ ↦ star x * x) a := by
    cfc_pull ℂ a
  trivial

/- The block is handed the side goals and nothing else, so on a pull that left none it has no
goal to work on. `all_goals ..` is the way to write a block that tolerates an empty list. -/
/-- error: No goals to be solved -/
#guard_msgs in
example (ha : IsStarNormal a) : star a + b = cfc (fun x : ℂ ↦ star x) a + b := by
  conv_lhs => arg 1; cfc_pull ℂ a => exact ha

/-! #### The lemma list -/

/- `-foo` is only meaningful for a lemma that is in the set to begin with; a name that is not
there is much more likely to be a typo than a no-op the user wanted. -/
/--
error: `Nat.add_comm` is not in the `cfc_pull` lemma set, so `-Nat.add_comm` has nothing to remove
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [-Nat.add_comm] ℂ a

/- A lemma added at the call site is classified exactly as `@[cfc_pull]` would classify it, and
is rejected here for the same reasons and with the same message, reported at the name. -/
/--
error: @[cfc_pull] failed: neither side of `Nat.add_comm` has `cfc` or `cfcₙ`
as its head symbol:
  ?n + ?m = ?m + ?n
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [Nat.add_comm] ℂ a

/- Only declaration names may be listed. A local hypothesis is what `simp` would take here, so
the message says why this is not `simp`. -/
/--
error: `hf` is a local hypothesis, and `cfc_pull`'s lemma list takes declaration names only: a
  `@[cfc_pull]` lemma is instantiated from its constant, so there is nothing for a hypothesis to
  be. Rewrite with it first, as in `rw [hf]`.
-/
#guard_msgs (whitespace := lax) in
example (ha : IsStarNormal a) (f : ℂ → ℂ) (hf : star a = cfc f a) :
    star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [hf] ℂ a

end Tactic

section Attribute

/-! ### Failures of the `@[cfc_pull]` attribute -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- error: `cfcPullTest.notAnEquation` is not an equation -/
#guard_msgs in
@[cfc_pull] theorem cfcPullTest.notAnEquation : True := trivial


omit [Ring A] [StarRing A] [TopologicalSpace A] in
/--
error: @[cfc_pull] failed: neither side of `cfcPullTest.noCFC` has `cfc` or `cfcₙ`
as its head symbol:
  ?a = ?a
-/
#guard_msgs in
-- NB: LeanOA lints its whole library, where mathlib does not lint `MathlibTest`; being a
-- syntactic tautology is the point of this fixture.
@[cfc_pull, nolint synTaut] theorem cfcPullTest.noCFC (a : A) : a = a := rfl


/--
error: @[cfc_pull] failed: both sides of `cfcPullTest.sameSides` are applications of the same
functional calculus to the same element; there is nothing for `cfc_pull` to do.
-/
#guard_msgs in
@[cfc_pull, nolint synTaut]
theorem cfcPullTest.sameSides (f : R → R) (a : A) : cfc f a = cfc f a := rfl


/--
error: @[cfc_pull] failed: `cfcPullTest.equalSizes` looks like a composition lemma, but neither
side applies the functional calculus to a more complicated element than the other.
-/
#guard_msgs in
@[cfc_pull]
theorem cfcPullTest.equalSizes (f : R → R) (a b : A) (h : a = b) : cfc f a = cfc f b := by rw [h]


/--
error: @[cfc_pull] failed: the non-`cfc` side of `cfcPullTest.noHead` is `?b`,
which has no head symbol to index on.
-/
#guard_msgs in
@[cfc_pull] theorem cfcPullTest.noHead (f : R → R) (a b : A) (h : cfc f a = b) : cfc f a = b := h

end Attribute

section BothChange

/--
error: @[cfc_pull] failed: `cfcPullTest.ringAndUnitality` changes both the scalar ring and the
unitality of the functional calculus; such lemmas are not supported.
-/
#guard_msgs in
@[cfc_pull]
theorem cfcPullTest.ringAndUnitality {A : Type*} [CStarAlgebra A] {a : A} (f : ℝ → ℝ)
    (hf : ContinuousOn f (quasispectrum ℝ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfc (fun x : ℂ ↦ (f x.re : ℂ)) a := by
  rw [cfcₙ_eq_cfc, cfc_real_eq_complex]

end BothChange

section RingAndElement

/- `cfc_comp_re` and its three siblings change the scalar ring *and* the element. The `Scalar`
category cannot express that — `convert` applies a scalar lemma expecting the element to survive
— and the `Compose` category cannot either, since it is indexed at a single ring. So they are
rejected rather than silently entered as a bogus `ℂ → ℝ` conversion edge. -/

/--
error: @[cfc_pull] failed: `cfc_comp_re` changes both the scalar ring and the
element of the functional calculus; such lemmas are not supported. A scalar
conversion must leave the element alone, and a composition must leave the scalar
ring alone.
-/
#guard_msgs in
attribute [cfc_pull] cfc_comp_re

end RingAndElement

section UndeterminedVariable

/- A tagged lemma is rejected at *use* time, not at tagging time, when its statement leaves one of
its variables undetermined. `cfc_map_prod`'s auxiliary scalar ring `S` occurs only in its
hypotheses and instance arguments, so the lemma enters the database but can never be applied;
this is why it and `cfcₙ_map_prod` are left untagged in Mathlib. `set_option
trace.Tactic.cfc_pull true` reports the reason: the instance argument `CommRing ?S` is not
determined. -/

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] {a : A} {b : B}

attribute [local cfc_pull] cfc_map_prod

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `(cfc f a, cfc f b)`
    (head symbol: Prod.mk, target: cfc over ℂ at `(a, b)`)
-/
#guard_msgs in
example (f : ℂ → ℂ) (hab : IsStarNormal (a, b)) :
    (cfc f a, cfc f b) = cfc f (a, b) := by
  cfc_pull ℂ (a, b)

end UndeterminedVariable

section BoundHoles

/--
warning: `cfc_sum` applies the functional calculus at
  cfc (?f #0) ?a
which mentions a bound variable. `cfc_pull` cannot recurse under a binder, so it will
treat that position as part of the pattern rather than as a hole: the lemma will only
apply when the position is already an application of the calculus.

If that is what you intend, silence this warning with
`set_option cfcPull.warnBoundHoles false in`.
-/
#guard_msgs in
attribute [cfc_pull] cfc_sum

end BoundHoles
