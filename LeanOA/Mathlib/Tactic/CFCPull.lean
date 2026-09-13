/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull.Core
public meta import LeanOA.Mathlib.Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Conv.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# The `cfc_pull` tactic

The user-facing side of `cfc_pull`: syntax, elaboration of the scalar ring and the element,
locating the subterms of the goal to rewrite, and post-processing the side goals.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta Elab Tactic

/-- The value of a tactic-valued option: `(opt := by tac)` sets it to `tac`, and `(opt := none)`
turns it off, so that side goals of that kind are deferred unattempted. -/
def elabTacOption (item : ConfigEval.ConfigItem) : TermElabM (Option (TSyntax `tactic)) := do
  match item.value with
  -- parenthesised so that a multi-tactic sequence stays one tactic
  | `(by $seq) => return some (← `(tactic| ($seq)))
  | `(none) => return none
  | _ => throwErrorAt item.value "expected `by tac` or `none`"

/-- Elaborate the configuration of `cfc_pull`. The tactic-valued fields take `by tac` or `none`
through `elabTacOption`. `discharger` is omitted; `mkConfig` fills it in from the
`(disch := ..)` clause. -/
declare_config_elab elabCFCPullConfig Config where
  omit discharger
  option contTac := fun cfg item => do
    item.addConstInfo ``Config.contTac
    return { cfg with contTac := ← elabTacOption item }
  option mapZeroTac := fun cfg item => do
    item.addConstInfo ``Config.mapZeroTac
    return { cfg with mapZeroTac := ← elabTacOption item }
  option predTac := fun cfg item => do
    item.addConstInfo ``Config.predTac
    return { cfg with predTac := ← elabTacOption item }

/-! ### Side goals -/

/-- Run a tactic on a goal, returning `true` iff it closes the goal; otherwise restore the state. -/
def tryTacticOn (g : MVarId) (tac : TacticM Unit) : TacticM Bool :=
  tryTactic do unless (← Tactic.run g tac).isEmpty do failure

/-- The tactic to try on a side goal of this kind, if any. This returns `TSyntax` as opposed to
`TacticM Unit` because we also want it to appear in traces. -/
def SideGoalKind.tactic? (cfg : Config) : SideGoalKind → Option (TSyntax `tactic)
  | .continuity => cfg.contTac
  | .mapZero => cfg.mapZeroTac
  | .predicate => cfg.predTac
  | .other => cfg.discharger

/-- Deduplicate side goals and try to close them with the appropriate tactic, including the user
provided discharger for `SideGoalKind.other` goals. With `+deferAll` no attempt is made.
Unless `defer` is set (there is a `=> ..` block to hand them to), surviving goals are an error. -/
def postProcessSideGoals (cfg : Config) (goals : Array (MVarId × SideGoalKind))
    (defer : Bool) : TacticM (Array MVarId) := do
  let mut out := #[]
  for (g, kind) in goals do
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
    if ← withReducible g.assumptionCore then
      trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `assumption`"
      continue
    if let some tac := kind.tactic? cfg then
      if ← tryTacticOn g (evalTactic tac) then
        trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `{tac}`"
        continue
    else
      trace[Tactic.cfc_pull] "deferring `{type}` unattempted (no discharger for `{kind.tag}` goals)"
      out := out.push g
      continue
    trace[Tactic.cfc_pull] "{crossEmoji} could not close `{type}`"
    out := out.push g
  unless defer || cfg.deferAll || out.isEmpty do
    throwError "`cfc_pull` rewrote the goal but could not discharge \
      {out.size} side goal{if out.size == 1 then "" else "s"}:\
      {indentD (goalsToMessageData out.toList)}\n\
      Discharge them with a tactic block, as in `cfc_pull .. => tac`."
  return out

/-! ### Locating the arguments to pull -/

/-- The positions in the target that `cfc_pull` should act on: those arguments of the head
application whose type is the algebra `A`. For `lhs = rhs` these are `lhs` and `rhs`; for
`lhs ≤ rhs` likewise. -/
def targetPositions (target alg : Expr) : MetaM (Array Nat) := do
  let args := target.getAppArgs
  let mut out := #[]
  for _h : i in [0:args.size] do
    if ← withReducible (isDefEq (← inferType args[i]) alg) then
      out := out.push i
  return out

/-! ### The lemma list -/

/-- Remove the identifier from the lemma database of `cfc_pull` for this call. -/
syntax cfcPullErase := "-" ident

/-- `cfc_pull`'s bracketed lemma list, which adjusts the `@[cfc_pull]` set for one call. -/
syntax cfcPullLemmas := " [" withoutPosition((cfcPullErase <|> ident),*,?) "]"

/-- Apply the bracketed lemma list to the `@[cfc_pull]` set. Only global declarations allowed. -/
def elabCFCPullLemmas (lemmas : Lemmas) (stx? : Option (TSyntax ``cfcPullLemmas)) :
    TacticM Lemmas := do
  let some stx := stx? | return lemmas
  let mut lemmas := lemmas
  for arg in stx.raw[1].getSepArgs do
    if arg.isOfKind ``cfcPullErase then
      let id : Ident := ⟨arg[1]⟩
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      unless lemmas.contains declName do
        throwErrorAt id "`{ppConst declName}` is not in the `cfc_pull` lemma set, so \
          `-{id}` has nothing to remove"
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
result, unless `rfl` closes it. The surviving side goals are handed to the tactic in `refTac?`
(the `=> ..` block) if there is one, and otherwise (with `+deferAll`) follow the new goal in the
goal list. The syntax in `refTac?` is the `=>`, where goals the block leaves open are reported. -/
def cfcPullTarget (cfg : Config) (lemmas : Lemmas) (R elem : Expr) (goal : MVarId)
    (refTac? : Option (Syntax × TacticM Unit)) : TacticM Unit := do
  let alg ← inferType elem
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let positions ← targetPositions target alg
  if positions.isEmpty then
    throwError "`cfc_pull` found nothing of type `{alg}` in the goal{indentExpr target}"
  let args := target.getAppArgs
  let mut newArgs := args
  let mut proofs := #[]
  let mut sideGoals := #[]
  let mut changed := false
  -- the failures are kept as `MessageData`, so that the expressions in them are pretty-printed
  -- in the reader's context; the string alongside is only the key that deduplicates them
  let mut failures : Array (String × MessageData) := #[]
  for i in positions do
    let arg := args[i]!
    let mctx ← getMCtx
    let attempt : Except MessageData (Expr × Expr × Array (MVarId × SideGoalKind)) ← (do
      try
        return .ok (← runPull cfg lemmas R elem arg)
      catch ex =>
        setMCtx mctx
        return .error ex.toMessageData)
    match attempt with
    | .ok (newArg, proof, goals) =>
      newArgs := newArgs.set! i newArg
      proofs := proofs.push proof
      sideGoals := sideGoals ++ goals
      unless newArg == arg do changed := true
    | .error msg =>
      -- the two sides of a relation usually fail for the same reason; do not say so twice
      let key ← msg.toString
      unless failures.any (·.1 == key) do failures := failures.push (key, msg)
      proofs := proofs.push (← mkEqRefl arg)
  unless changed do
    throwError "`cfc_pull` made no progress\
      {indentD (MessageData.joinSep (failures.toList.map (·.2)) m!"\n")}"
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
  if ← tryTacticOn newGoal (evalTactic (← `(tactic| with_reducible rfl))) then
    main := []
  let survivors ← postProcessSideGoals cfg sideGoals (defer := refTac?.isSome)
  replaceMainGoal (main ++ survivors.toList)
  let some (ref, tac) := refTac? | return
  withRef ref <| focusGoalsAndDone survivors.contains tac

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

In the following example, `cfc_pull` acts on both sides of the equality, doing nothing with the
right-hand side, but expressing the left-hand side as `cfc (?f : R → R) a` where
`?f := fun x : R ↦ star x * x`, and the goal is closed with `rfl` at reducible transparency.

```lean
example (ha : p a) : star a * a = cfc (eun x : R ↦ star x * x) a := by
  cfc_pull R a
```

* `cfc_pull R a`: with `a : A` attempts to write maximal subexpressions of the goal with type `A` in
  the form `cfc f a` for some function `f : R → R`. Fails if any generated side goals cannot be
  solved automatically.
* `cfc_pull -unital R a`: the same, but for `cfcₙ` instead; if only a non-unital instance of
  the continuous functional calculus can be found this is the default, whereas `cfc` is the default
  if a unital instance is found.
* `cfc_pull R a => tacticSeq`: discharge the side goals left unsolved with the supplied tactic
  script, which sees only those goals and must close all of them. `case cfc_pull.continuity => ..`
  and so on select goals by kind.
* `cfc_pull +deferAll R a`: attempt to discharge no side goals; they are returned to the user (or
  handed to the `=> ..` block, if there is one).
* `cfc_pull [lemma1, -lemma2] R a`: add `lemma1` to the list of lemmas used by `cfc_pull`, and
  remove `lemma2`; only global declaration name are permitted.
* `cfc_pull +zetaDelta R a`: unfold `let`-bound variables.
* `cfc_pull (disch := tac) R a`: run `tac` to attempt to discharge side goals (only applicable
  for side goals in the category `cfc_pull.side`).
* `cfc_pull (contTac := by tac) R a`: run `tac` instead of `cfc_cont_tac` on `cfc_pull.continuity`
  side goals; likewise `mapZeroTac` (default `cfc_zero_tac`) for `cfc_pull.mapZero` goals and
  `predTac` for `cfc_pull.predicate` goals. `(contTac := none)` and so on skip the tactic entirely,
  so only `assumption` is tried.

Detailed tracing can be enabled with `set_option trace.Tactic.cfc_pull true` showing which lemmas
were tried and why they failed, which side goals were generated, or discharged.
-/
syntax (name := cfcPull) "cfc_pull" optConfig (discharger)? (cfcPullLemmas)?
  ppSpace colGt term:max ppSpace colGt term:max
  (" => " tacticSeq)? : tactic

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
  let `(tactic| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $ring $elem
      $[=>%$arrow? $tac?]?) := stx
    | throwUnsupportedSyntax
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem) ← elabRingAndElem ring elem
  let refTac? := return (← arrow?, evalTactic (← tac?))
  cfcPullTarget (← mkConfig cfg disch?) lemmas R elem (← getMainGoal) refTac?

/-- Elaborator for `cfc_pull` in `conv` mode. -/
@[tactic cfcPullConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let `(conv| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $ring $elem
      $[=>%$arrow? $tac?]?) := stx
    | throwUnsupportedSyntax
  let lhs := (← Conv.getLhs).consumeMData
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem) ← elabRingAndElem ring elem
  let cfg ← mkConfig cfg disch?
  let (newLhs, proof, sideGoals) ← runPull cfg lemmas R elem lhs
  Conv.updateLhs newLhs proof
  let sideGoals ← postProcessSideGoals cfg sideGoals (defer := tac?.isSome)
  appendGoals sideGoals.toList
  let (some arrow, some tac) := (arrow?, tac?) | return
  withRef arrow <| focusGoalsAndDone sideGoals.contains (evalTactic tac)

end Mathlib.Tactic.CFCPull
