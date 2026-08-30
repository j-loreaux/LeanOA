/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull.Core
public meta import Lean.Elab.Tactic.Conv.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# The `cfc_pull` tactic

The user-facing side of `cfc_pull`: syntax, elaboration of the scalar ring and the element,
locating the subterms of the goal to rewrite, and post-processing the side goals.

See `LeanOA/Mathlib/Tactic/CFCPull/Spec.md` for the specification.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta Elab Tactic

/-- Elaborate the configuration of `cfc_pull`. `discharger` is omitted because its value is a
tactic rather than a term; `mkConfig` fills it in from the `(disch := ..)` clause. -/
declare_config_elab elabCFCPullConfig Config where
  omit discharger

/-! ### Side goals -/

/-- Run a tactic on a goal, returning `true` if it closed the goal and restoring the state
otherwise. -/
def tryTacticOn (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    if (← Tactic.run g (evalTactic tac)).isEmpty then
      return true
  catch _ => pure ()
  s.restore
  return false

/-- The auto-param tactic that the continuous functional calculus API itself would use for a
hypothesis of this kind.

`.other` gets the predicate tactic too. Its classification is deliberately coarse (see
`SideGoalKind.ofType`), so a goal landing there is often a predicate goal in disguise: `0 ≤ a * a`
is the predicate of the calculus over `ℝ≥0`, but is not recognised as one. -/
def SideGoalKind.tactic : SideGoalKind → MetaM (TSyntax `tactic)
  | .continuity => `(tactic| cfc_cont_tac)
  | .mapZero => `(tactic| cfc_zero_tac)
  | .predicate | .other =>
    -- `cfc_predicate` closes the predicate goals for the inner element of a composition, e.g.
    -- `p (cfc g a)`; the identifiers are built unresolved so that they are looked up in the
    -- user's environment rather than in this file's.  Note that `cfc_tac` never fails, so it
    -- has to come last.
    `(tactic| first
      | exact $(mkIdent `cfc_predicate) _ _
      | exact $(mkIdent `cfcₙ_predicate) _ _
      | cfc_tac)

/-- Try to close the side goals raised by the pull: `assumption` first, then the auto-param
tactic for the goal's kind, and finally — for the goals the calculus API has no auto-param for —
`cfg.discharger`. Duplicates are merged, which matters because the two sides of a relation are
pulled independently and so tend to ask for the same predicate twice.

Whatever survives is an error unless `+defer` was given, in which case it is returned to be added
to the goal list. With `+deferAll` no goal is attempted at all, and every one of them is
returned; they are still merged, so that the deferred list has no repetitions in it. -/
def postProcessSideGoals (cfg : Config) (goals : Array MVarId) : TacticM (Array MVarId) := do
  let mut out := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let type ← instantiateMVars (← g.getType)
    -- merge with an earlier goal of the same type
    if ← out.anyM fun g' => do
        if ← withReducible <| isDefEq type (← g'.getType) then
          g.assign (mkMVar g'); return true
        else return false then
      trace[Tactic.cfc_pull] "side goal `{type}` is a duplicate"
      continue
    if cfg.deferAll then
      trace[Tactic.cfc_pull] "deferring `{type}` unattempted (`+deferAll`)"
      out := out.push g
      continue
    if ← g.assumptionCore then
      trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `assumption`"
      continue
    let kind := SideGoalKind.ofTag (← g.getTag)
    let tac ← kind.tactic
    if ← tryTacticOn g tac then
      trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `{tac}`"
      continue
    /- The user's discharger is the last resort, and only for `.other`: the hypotheses peculiar
    to an individual `@[cfc_pull]` lemma, which the calculus API has no tactic for. It is run
    separately rather than appended to `kind.tactic` with `first`, because that tactic ends in
    `cfc_tac`, which never fails and so would swallow the alternative. -/
    if kind == .other then
      if let some disch := cfg.discharger then
        if ← tryTacticOn g disch then
          trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with the discharger `{disch}`"
          continue
    trace[Tactic.cfc_pull] "{crossEmoji} could not close `{type}`"
    out := out.push g
  unless cfg.defer || cfg.deferAll || out.isEmpty do
    throwError "`cfc_pull` rewrote the goal but could not discharge \
      {out.size} side goal{if out.size == 1 then "" else "s"}:\
      {indentD (goalsToMessageData out.toList)}\n\
      Use `cfc_pull +defer ..` to have them added to the goal list instead."
  return out

/-! ### Locating the arguments to pull -/

/-- The positions in the target that `cfc_pull` should act on: those arguments of the head
application whose type is the algebra `A`. For `lhs = rhs` these are `lhs` and `rhs`; for
`lhs ≤ rhs` likewise. -/
def targetPositions (target alg : Expr) : MetaM (Array Nat) := do
  let args := target.getAppArgs
  let mut out := #[]
  for _h : i in [0:args.size] do
    if ← isDefEq (← inferType args[i]) alg then
      out := out.push i
  return out

/-! ### The lemma list -/

/-- `-foo`: the entry of `cfc_pull`'s bracketed lemma list that removes every entry for `foo`
from the set for this call. -/
syntax cfcPullErase := "-" ident

/-- `cfc_pull`'s bracketed lemma list, which adjusts the `@[cfc_pull]` set for one call. Each
entry is either a declaration name, added to the set exactly as `@[cfc_pull]` would add it, or
`-foo`, which takes `foo` out. -/
syntax cfcPullLemmas := " [" withoutPosition((cfcPullErase <|> ident),*,?) "]"

/-- Apply the bracketed lemma list to the `@[cfc_pull]` set, giving the set that this call will
pull with. The database itself is untouched: there is no way to remove a lemma from it.

Only global declarations may be named. A tagged lemma is instantiated from its constant — see
`instantiateLemma` — so a local hypothesis has no place in the set; `rw` is the way to use one.
An added lemma is classified exactly as the attribute would classify it (`mkEntry`), and so is
read in the direction it is stated, rejected here for the same reasons, and given the default
priority. -/
def elabCFCPullLemmas (lemmas : Lemmas) (stx? : Option (TSyntax ``cfcPullLemmas)) :
    TacticM Lemmas := do
  let some stx := stx? | return lemmas
  let mut lemmas := lemmas
  for arg in stx.raw[1].getSepArgs do
    if arg.isOfKind ``cfcPullErase then
      let id : Ident := ⟨arg[1]⟩
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      unless lemmas.contains declName do
        throwErrorAt id "`{declName}` is not in the `cfc_pull` lemma set, so `-{id}` has \
          nothing to remove"
      lemmas := lemmas.erase declName
    else
      let id : Ident := ⟨arg⟩
      -- a local hypothesis is the natural thing to try here, `simp` taking one; the "unknown
      -- constant" that `realizeGlobalConstNoOverloadWithInfo` would report does not say why
      if (← getLCtx).findFromUserName? id.getId |>.isSome then
        throwErrorAt id "`{id}` is a local hypothesis, and `cfc_pull`'s lemma list takes \
          declaration names only: a `@[cfc_pull]` lemma is instantiated from its constant, so \
          there is nothing for a hypothesis to be. Rewrite with it first, as in `rw [{id}]`."
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      -- `withRef` points a rejection, or a `warnBoundHoles` warning, at the offending name
      let entry ← withRef id <| mkEntry declName (prio := eval_prio default)
      lemmas := lemmas.addEntry entry
  return lemmas

/-! ### The tactic -/

/-- Pull every argument of the target that lives in the algebra, and replace the goal by the
result. Returns the new goal (unless it was closed by `rfl`) and the surviving side goals. -/
def cfcPullTarget (cfg : Config) (lemmas : Lemmas) (R elem : Expr) (goal : MVarId) :
    TacticM Unit := do
  let alg ← inferType elem
  -- `consumeMData` is not optional: a goal type routinely arrives wrapped in an
  -- `mdata noImplicitLambda` annotation left by the elaborator, and `Expr.getAppArgs` does not
  -- see through `mdata`, so `targetPositions` below would find no arguments at all.
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let positions ← targetPositions target alg
  if positions.isEmpty then
    throwError "`cfc_pull` found nothing of type `{alg}` in the goal{indentExpr target}"
  let args := target.getAppArgs
  let mut newArgs := args
  let mut proofs := #[]
  let mut sideGoals := #[]
  let mut changed := false
  let mut failures : Array String := #[]
  for i in positions do
    let arg := args[i]!
    let mctx ← getMCtx
    let attempt : Except String (Expr × Expr × Array MVarId) ← (do
      try
        return .ok (← runPull cfg lemmas R elem arg)
      catch ex =>
        setMCtx mctx
        return .error (← ex.toMessageData.toString))
    match attempt with
    | .ok (newArg, proof, goals) =>
      newArgs := newArgs.set! i newArg
      proofs := proofs.push proof
      sideGoals := sideGoals ++ goals
      unless newArg == arg do changed := true
    | .error msg =>
      -- the two sides of a relation usually fail for the same reason; do not say so twice
      unless failures.contains msg do failures := failures.push msg
      proofs := proofs.push (← mkEqRefl arg)
  unless changed do
    throwError "`cfc_pull` made no progress\
      {indentD (MessageData.joinSep (failures.toList.map (m!"{·}")) m!"\n")}"
  -- Rebuild the goal by congruence over the positions we changed.
  let newTarget := mkAppN target.getAppFn newArgs
  let hcongr ← withLocalDeclsD (positions.map fun _ => (`x, fun _ => pure alg)) fun xs => do
    let mut body := args
    for _h : j in [0:positions.size] do
      body := body.set! positions[j]! xs[j]!
    let F ← mkLambdaFVars xs (mkAppN target.getAppFn body)
    -- `mkCongr` one position at a time: from `hᵢ : xᵢ = yᵢ`, folding it over `rfl : F = F`
    -- gives `F x₀ ⋯ xₙ = F y₀ ⋯ yₙ`. `F` is non-dependent by construction.
    proofs.foldlM (init := ← mkEqRefl F) fun h h' => mkCongr h h'
  let hcongr ← mkExpectedTypeHint hcongr (← mkEq target newTarget)
  let newGoal ← goal.replaceTargetEq newTarget hcongr
  let mut main := [newGoal]
  if ← tryTacticOn newGoal (← `(tactic| rfl)) then
    main := []
  replaceMainGoal (main ++ (← postProcessSideGoals cfg sideGoals).toList)

/-- Elaborate the scalar ring and the element. -/
def elabRingAndElem (ring elem : Term) : TacticM (Expr × Expr) := do
  let R ← Term.elabType ring
  let elem ← Term.elabTerm elem none
  Term.synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars R, ← instantiateMVars elem)

open Lean Parser Tactic
/--
`cfc_pull R a` rewrites the goal so that the continuous functional calculus is at the head of
maximal subexpressions whose type matches that of `a`: each such subexpression is replaced by
`cfc f a` (or `cfcₙ f a`) for some function `f : R → R` that the tactic determines from the
structure of the expression and the collection of lemmas tagged `@[cfc_pull]`.

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a
```

* `cfc_pull R a`: with `a : A` attempts to write maximal subexpressions of the goal with type `A` in
  the form `cfc f a` for some function `f : R → R`. Fails if any generated side goals cannot be
  solved automatically.
* `cfc_pull -unital R a`: the same, but for `cfcₙ` instead; if only a non-unital instance of
  the continuous functional calculus can be found this is the default, whereas `cfc` is the default
  if a unital instance is found.
* `cfc_pull +defer R a`: return unsolved side goals to the user, instead of failing.
* `cfc_pull +deferAll R a`: return all side goals to the user.
* `cfc_pull [lemma1, -lemma2] R a`: add `lemma1` to the list of lemmas used by `cfc_pull`, and
  remove `lemma2`; only global declaration name are permitted.
* `cfc_pull +zetaDelta R a`: unfold `let`-bound variables.
* `cfc_pull (disch := tac) R a`: run `tac` to attempt to discharge side goals (only applicable
  for side goals in the category `cfc_pull.side`).
* `cfc_pull R a => tacticSeq` (`conv` mode only): discharge unsolved side goals with the supplied
  tactic script (implies `+defer`).

Detailed tracing can be enabled with `set_option trace.Tactic.cfc_pull true` showing which lemmas
were tried and why they failed, which side goals were generated, or discharged.
-/
syntax (name := cfcPull) "cfc_pull" optConfig (discharger)? (cfcPullLemmas)?
  ppSpace colGt term:max ppSpace colGt term:max : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull" optConfig (discharger)? (cfcPullLemmas)?
  ppSpace colGt term:max ppSpace colGt term:max
  (" => " tacticSeq)? : conv

/-- Read the configuration, together with the `(disch := ..)` clause, which
`elabCFCPullConfig` cannot see. -/
def mkConfig (cfgStx : TSyntax ``optConfig) (disch? : Option (TSyntax ``discharger)) :
    TacticM Config := do
  let mut cfg ← elabCFCPullConfig cfgStx
  if let some disch := disch? then
    -- the keyword is `patternIgnore`d in the parser, so it does not appear in the tree
    let `(discharger| ($_ := $tac)) := disch | throwUnsupportedSyntax
    -- parenthesised so that a multi-tactic sequence stays one tactic
    cfg := { cfg with discharger := some (← `(tactic| ($tac))) }
  return cfg

/-- Elaborator for the `cfc_pull` tactic. -/
@[tactic cfcPull]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let `(tactic| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $ring $elem) := stx
    | throwUnsupportedSyntax
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem) ← elabRingAndElem ring elem
  cfcPullTarget (← mkConfig cfg disch?) lemmas R elem (← getMainGoal)

/-- Elaborator for `cfc_pull` in `conv` mode. -/
@[tactic cfcPullConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let `(conv| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $ring $elem
      $[=> $tac?]?) := stx
    | throwUnsupportedSyntax
  let lhs := (← Conv.getLhs).consumeMData
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem) ← elabRingAndElem ring elem
  let mut cfg ← mkConfig cfg disch?
  /- A `=> tac` block is what disposes of the survivors, so `postProcessSideGoals` must hand
  them over rather than report them: the block implies `+defer`. It does not imply `+deferAll` —
  the auto-param tactics still run, and the block sees only what they left, exactly as the
  tactic after `cfc_pull +defer ..` does in tactic mode. -/
  if tac?.isSome then cfg := { cfg with defer := true }
  let (newLhs, proof, sideGoals) ← runPull cfg lemmas R elem lhs
  Conv.updateLhs newLhs proof
  let sideGoals ← postProcessSideGoals cfg sideGoals
  let some tac := tac? | replaceMainGoal ((← getGoals) ++ sideGoals.toList)
  /- Run the block with the side goals, and only those, as the goal list: the `conv` goal is set
  aside so that the block cannot touch it, and restored afterwards. Handing over the whole list
  rather than one goal at a time is what lets `case cfc_pull.continuity => ..` be written here,
  the goals having kept their kind tags. -/
  let convGoals ← getGoals
  setGoals sideGoals.toList
  evalTactic tac
  let remaining ← getGoals
  unless remaining.isEmpty do
    throwError "`cfc_pull` ran the `=> ..` block, but {remaining.length} side \
      goal{if remaining.length == 1 then " is" else "s are"} still open:\
      {indentD (goalsToMessageData remaining)}\n\
      A `conv` block cannot end with unsolved goals, so the `=> ..` block must close every one."
  setGoals convGoals

end Mathlib.Tactic.CFCPull
