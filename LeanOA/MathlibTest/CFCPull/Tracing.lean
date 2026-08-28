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
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Tags
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Inspecting what `cfc_pull` is doing

`set_option trace.Tactic.cfc_pull true` makes `cfc_pull` report its reasoning as a tree: one node
per subexpression it recurses into, and inside each node the candidate lemmas retrieved from the
`@[cfc_pull]` index, which of them were rejected and why, which hypotheses were filled from the
shared predicate proof and which were deferred as side goals, which conversions were applied,
and finally what became of each side goal.

This file is both a demonstration and a regression test for that output. `#cfc_pull_lemmas`, at
the end, prints the lemma database itself.
-/

@[expose] public section

-- NB: LeanOA sets `pp.unicode.fun` package-wide, where mathlib's `MathlibTest` library does not,
-- so the expected messages below print `fun x ↦ _` where upstream they print `fun x => _`.

open scoped NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

/-! ### A successful pull

The predicate for the mode is reported once, before the traversal starts. Each node says what it
is pulling and into which mode; `✅️` marks the ones that succeeded. Here the recursion stops
immediately, because `cfc_star_id` matches `star a` outright and needs no holes. -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull star a into a cfc over ℂ
  [Tactic.cfc_pull] candidates: [cfc_star_id, cfc_star, cfcₙ_star_id, cfcₙ_star]
  [Tactic.cfc_pull] `cfc_star_id`: filled `IsStarNormal a` from the shared predicate proof
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ star x) a into a cfc over ℂ
[Tactic.cfc_pull] ✅️ closed `IsStarNormal a` with `assumption`
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStarNormal a) : star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull ℂ a

/-! ### The lemma list

The candidate list is where a bracketed `[..]` shows up: `-cfc_star_id` takes that lemma out for
this call, and the pull falls through to `cfc_star`, whose algebraic side `star (cfc f a)` has a
hole — hence the extra node for the recursion into `a`. -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull star a into a cfc over ℂ
  [Tactic.cfc_pull] candidates: [cfc_star, cfcₙ_star_id, cfcₙ_star]
  [Tactic.cfc_pull] ✅️ pull a into a cfc over ℂ
    [Tactic.cfc_pull] `cfc_id'`: filled `IsStarNormal a` from the shared predicate proof
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ star x) a into a cfc over ℂ
[Tactic.cfc_pull] ✅️ closed `IsStarNormal a` with `assumption`
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStarNormal a) : star a = cfc (fun x : ℂ ↦ star x) a := by
  cfc_pull [-cfc_star_id] ℂ a

/-! ### Backtracking

Candidates are tried best-first and the trace records each rejection with the reason. Here
`cfc_const_mul` and `cfc_const_mul_id` have the higher priority — they would produce
`fun x ↦ r * f x` rather than `fun x ↦ r • f x` — but the scalar is a natural number rather than
an element of `ℂ`, so both fail to match and `cfc_smul_id` wins. -/

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
  [Tactic.cfc_pull] ❌️ `cfc_const_mul_id` does not match: `?r • a` ≠ `3 • a`
  [Tactic.cfc_pull] ❌️ `cfc_const_mul` does not match: `?r • ?_` ≠ `3 • a`
  [Tactic.cfc_pull] `cfc_smul_id`: filled `IsStarNormal a` from the shared predicate proof
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ 3 • x) a into a cfc over ℂ
[Tactic.cfc_pull] ✅️ closed `IsStarNormal a` with `assumption`
-/
-- `pp.mvars.anonymous false` so that the unnamed metavariable in the rejected pattern prints as
-- `?_` rather than with an index that every edit above this point would shift
#guard_msgs in
set_option pp.mvars.anonymous false in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStarNormal a) : (3 : ℕ) • a = cfc (fun x : ℂ ↦ (3 : ℕ) • x) a := by
  cfc_pull ℂ a

/-! ### Conversions and deferred side goals

`a⁺` is naturally a `cfcₙ` over `ℝ`, so reaching a `cfc` over `ℂ` takes two conversions. The
trace shows the predicate being computed afresh for each mode along the way, which hypotheses
were deferred (they become side goals), and which were filled from the shared proof — note that
`IsSelfAdjoint a` is proved once and reused. -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull a⁺ into a cfc over ℂ
  [Tactic.cfc_pull] candidates: [CFC.posPart_def]
  [Tactic.cfc_pull] predicate for cfcₙ over ℝ is IsSelfAdjoint
  [Tactic.cfc_pull] `cfcₙ_eq_cfc`: deferred `ContinuousOn (fun x ↦ x⁺) (quasispectrum ℝ a)`
  [Tactic.cfc_pull] `cfcₙ_eq_cfc`: deferred `0⁺ = 0`
  [Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
  [Tactic.cfc_pull] `cfc_real_eq_complex`: filled `IsSelfAdjoint a` from the shared predicate proof
[Tactic.cfc_pull] predicate for cfc over ℂ is IsStarNormal
[Tactic.cfc_pull] ✅️ pull cfc (fun z ↦ ↑z.re⁺) a into a cfc over ℂ
[Tactic.cfc_pull] ✅️ closed `ContinuousOn (fun x ↦ x⁺) (quasispectrum ℝ a)` with `cfc_cont_tac`
[Tactic.cfc_pull] ✅️ closed `0⁺ = 0` with `cfc_zero_tac`
[Tactic.cfc_pull] ✅️ closed `IsSelfAdjoint a` with `assumption`
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsSelfAdjoint a) : a⁺ = cfc (fun z : ℂ ↦ (z.re⁺ : ℝ)) a := by
  cfc_pull ℂ a

/-! ### Side goals that could not be discharged

`Real.log` is not continuous at `0`, so `cfc_cont_tac` cannot prove the continuity hypothesis of
`cfc_mul` and the goal comes back to the user. The trace records the attempt, and `+defer` is
what turns the leftover into a goal rather than an error. -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull CFC.log a * CFC.log a into a cfc over ℝ
  [Tactic.cfc_pull] candidates: [cfc_mul, cfcₙ_mul]
  [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
    [Tactic.cfc_pull] candidates: [CFC.log_def]
  [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
    [Tactic.cfc_pull] candidates: [CFC.log_def]
  [Tactic.cfc_pull] `cfc_mul`: deferred `ContinuousOn Real.log (spectrum ℝ a)`
  [Tactic.cfc_pull] `cfc_mul`: deferred `ContinuousOn Real.log (spectrum ℝ a)`
[Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ Real.log x * Real.log x) a into a cfc over ℝ
[Tactic.cfc_pull] ❌️ could not close `ContinuousOn Real.log (spectrum ℝ a)`
[Tactic.cfc_pull] side goal `ContinuousOn Real.log (spectrum ℝ a)` is a duplicate
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +defer ℝ a
  case cfc_pull.continuity =>
    exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/-! ### Side goals nobody tried to discharge

`+deferAll` switches the discharging off: every side goal is reported as deferred unattempted
and handed back. Deduplication still runs — it comes first, before any attempt — which is why
`cfc_mul`'s two identical continuity hypotheses still produce one goal here, and why the trace
below ends in a `is a duplicate` line rather than a second `unattempted` one. -/

/--
trace: [Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull CFC.log a * CFC.log a into a cfc over ℝ
  [Tactic.cfc_pull] candidates: [cfc_mul, cfcₙ_mul]
  [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
    [Tactic.cfc_pull] candidates: [CFC.log_def]
  [Tactic.cfc_pull] ✅️ pull CFC.log a into a cfc over ℝ
    [Tactic.cfc_pull] candidates: [CFC.log_def]
  [Tactic.cfc_pull] `cfc_mul`: deferred `ContinuousOn Real.log (spectrum ℝ a)`
  [Tactic.cfc_pull] `cfc_mul`: deferred `ContinuousOn Real.log (spectrum ℝ a)`
[Tactic.cfc_pull] predicate for cfc over ℝ is IsSelfAdjoint
[Tactic.cfc_pull] ✅️ pull cfc (fun x ↦ Real.log x * Real.log x) a into a cfc over ℝ
[Tactic.cfc_pull] deferring `ContinuousOn Real.log (spectrum ℝ a)` unattempted (`+deferAll`)
[Tactic.cfc_pull] side goal `ContinuousOn Real.log (spectrum ℝ a)` is a duplicate
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +deferAll ℝ a
  exact Real.continuousOn_log.mono fun x hx h ↦ spectrum.zero_notMem ℝ ha.2 (h ▸ hx)

/-! ### A failure

When the tactic gets stuck, the trace is the way to find out why. `💥️` marks the node that
failed, and the reason here is that the only lemma indexed under `PosPart.posPart` lives over
`ℝ`, from which — with `cfc_real_eq_nnreal` and its non-unital counterpart taken out of the set
— there is no conversion to the requested `ℝ≥0`, so it is not even offered as a candidate. The
error message reports the head symbol and the element being pulled towards, but not that
reason.

(The removal is what makes the failure happen: with the whole set, `ℝ≥0`, `ℝ` and `ℂ` are all
reachable from one another, and this pull instead succeeds and leaves the `0 ≤ a` that
`cfc_real_eq_nnreal` asks for as a side goal.) -/

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `a⁺`
    (head symbol: PosPart.posPart, target: cfc over ℝ≥0 at `a`)
---
trace: [Tactic.cfc_pull] predicate for cfc over ℝ≥0 is fun x ↦ 0 ≤ x
[Tactic.cfc_pull] 💥️ pull a⁺ into a cfc over ℝ≥0
  [Tactic.cfc_pull] skipping `CFC.posPart_def`: no conversion from Real to NNReal
  [Tactic.cfc_pull] candidates: []
[Tactic.cfc_pull] predicate for cfc over ℝ≥0 is fun x ↦ 0 ≤ x
[Tactic.cfc_pull] 💥️ pull a⁺ into a cfc over ℝ≥0
  [Tactic.cfc_pull] skipping `CFC.posPart_def`: no conversion from Real to NNReal
  [Tactic.cfc_pull] candidates: []
-/
#guard_msgs in
set_option trace.Tactic.cfc_pull true in
example (ha : IsSelfAdjoint a) : a⁺ = a⁺ := by
  cfc_pull [-cfc_real_eq_nnreal, -cfcₙ_real_eq_nnreal] ℝ≥0 a

/-! ### The lemma database

`#cfc_pull_lemmas` prints every tagged lemma, grouped by category, with the information the
tactic indexes it under: its scalar ring (`_` for a lemma polymorphic in the ring), whether it is
about `cfc` or `cfcₙ`, how many holes its algebraic side has, and its priority. Composition
lemmas additionally show the head symbol of the element they match.

The output is long, so it is only checked for not failing here; run the command yourself to read
it. -/

#guard_msgs(drop info) in
#cfc_pull_lemmas
