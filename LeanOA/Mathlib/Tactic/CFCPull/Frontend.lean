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

/-! ### Determining the scalar ring and the element -/

/-- Find an application of `cfc` or `cfcₙ` inside `e`, outermost first. -/
def findCFCApp? (e : Expr) : Option CFCApp := do
  let s ← e.find? fun s => (CFCApp.match? s).isSome
  CFCApp.match? s

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

/-- Work out the scalar ring and the element from the goal when the user did not supply them:
look for an application of the calculus, preferring the later arguments of the target (i.e. the
right-hand side of a relation). Returns the `CFCApp` found. -/
def inferCFCApp (target : Expr) : MetaM CFCApp := do
  let args := target.getAppArgs
  for i in [0:args.size] do
    let arg := args[args.size - 1 - i]!
    if let some c := findCFCApp? arg then
      return c
  if let some c := findCFCApp? target then return c
  throwError "`cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from\n\
    which to read off the scalar ring and the element; supply them explicitly, as in\n\
    `cfc_pull ℝ a`"

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

/-- Elaborate the optional scalar ring and element arguments, falling back to reading them off
the goal. An argument written `_` is treated as absent, which is the way to give the element
without the ring. The `Option Bool` reports whether the calculus found in the goal (if any) was
unital, so that `cfc_pull` on a goal mentioning `cfcₙ` defaults to the non-unital calculus. -/
def elabRingAndElem (target : Expr) (ring? elem? : Option Term) :
    TacticM (Expr × Expr × Option Bool) := do
  /- The first explicit argument is the scalar ring.  Elaborating the element there is a natural
  mistake, so it gets a message of its own. -/
  let elabRing (r : Term) : TacticM Expr := do
    try
      Term.elabType r
    catch ex =>
      throwError "`cfc_pull`'s first argument is the scalar ring, but `{r}` did not elaborate \
        as a type:{indentD ex.toMessageData}\nIf `{r}` is the element to pull towards, give the \
        scalar ring too — or `_`, as in `cfc_pull _ {r}`."
  -- `_` in either position asks for that argument to be inferred, exactly as omitting it does
  let isHole (t : Term) : Bool := t.raw.isOfKind ``Lean.Parser.Term.hole
  match ring?.filter (!isHole ·), elem?.filter (!isHole ·) with
  | some r, some a =>
    let R ← elabRing r
    let elem ← Term.elabTerm a none
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars R, ← instantiateMVars elem, none)
  | some r, none =>
    let R ← elabRing r
    Term.synthesizeSyntheticMVarsNoPostponing
    let c ← inferCFCApp target
    return (← instantiateMVars R, c.a, some c.unital)
  | none, some a =>
    let elem ← Term.elabTerm a none
    Term.synthesizeSyntheticMVarsNoPostponing
    let c ← inferCFCApp target
    return (c.R, ← instantiateMVars elem, some c.unital)
  | none, none =>
    let c ← inferCFCApp target
    return (c.R, c.a, some c.unital)

/--
`cfc_pull R a` rewrites the goal so that the continuous functional calculus is at the head of
every expression in the algebra: each side of the goal is replaced by `cfc f a` (or `cfcₙ f a`)
for a function `f : R → R` that the tactic works out.

This automates the standard technique for proving identities in a C⋆-algebra: pull `cfc` to the
head on both sides, and then use `cfc_congr` to reduce to an equality of functions on the
spectrum. If both sides end up with the same function, `cfc_pull` closes the goal outright.

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a <;> fun_prop
```

Both arguments are optional: `cfc_pull` on its own reads the scalar ring and the element off an
application of `cfc`/`cfcₙ` already present in the goal, preferring the right-hand side. Writing
`_` for an argument asks for that one to be read off the goal, which is how to give the element
and leave the ring to be inferred:

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull _ a <;> fun_prop
```

The lemmas used along the way have hypotheses — continuity of the functions on the spectrum,
`f 0 = 0` in the non-unital case, and the predicate `p a` — and `cfc_pull` discharges them with
`assumption` and then with the auto-param tactic the calculus API itself uses (`cfc_cont_tac`,
`cfc_zero_tac`, `cfc_tac`). Anything left over is an error; `+defer` turns those into goals
instead, named after what they are, so that they can be addressed in groups:

```lean
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +defer ℝ a
  case cfc_pull.continuity => exact Real.continuousOn_log.mono fun x hx h ↦ ...
```

`+deferAll` goes further and switches the discharging off entirely, so that *every* hypothesis
the pull needed comes back as a goal — including the ones the auto-param tactics would have
closed. Use it to see what the pull really assumed, or to discharge the obligations by one
method of your own:

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull +deferAll R a <;> first | assumption | fun_prop
```

Configuration:

* `+unital` / `-unital` (default `+unital`): prefer the unital calculus `cfc`, or force the
  non-unital `cfcₙ`. With `+unital` the tactic falls back to `cfcₙ` in an algebra with no unital
  functional calculus.
* `+defer`: return the side goals that could not be discharged instead of failing.
* `+deferAll`: return *all* the side goals, without trying to discharge any of them. Implies
  `+defer`, and silently makes `(disch := ..)` inert — nothing is run on a side goal, the
  discharger included. Duplicates are merged either way, so a hypothesis that both sides of a
  relation ask for is handed back once.
* `(disch := tac)`: run `tac` on side goals that none of the above closed. Only the goals tagged
  `cfc_pull.side` reach it — the hypotheses peculiar to an individual `@[cfc_pull]` lemma, for
  which the calculus API has no auto-param tactic. As in `simp`, the default does nothing.
* `+zetaDelta`: unfold `let`-bound local variables. Off by default, so a local definition —
  written with `let`, or introduced by `set` — is an atom that the tactic does not look inside,
  and a pull reaching one gets stuck there. This is `simp`'s default too: `set b := star a * a
  with hb` is a request to stop reading `star a * a`, and unfolding it silently would undo the
  abstraction and strand `hb`. `rw [hb]` is the other way in. The *element* is unaffected —
  given as a `let`-bound variable it is matched, and returned, as written.
* `(maxDepth := n)`: the recursion depth limit.

In `conv` mode, `cfc_pull` acts on the current `conv` target, which is the way to pull at a
specific position:

```lean
example : star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv_lhs => cfc_pull R a
```

A `conv` block cannot end with unsolved goals — the same restriction that `rw` inside `conv` is
subject to — so a side goal that survives the discharging is fatal there, and deferring it is no
help. A trailing `=> tac` block is the way out: it takes the side goals, and only those, as its
goal list and must leave none of them open. It implies `+defer`, so the pull no longer errors on
what it could not close:

```lean
example : CFC.log a * CFC.log a + b = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a + b := by
  conv in CFC.log a * CFC.log a =>
    cfc_pull ℝ a => exact Real.continuousOn_log.mono fun x hx h ↦ ...
```

The lemma list, if there is one, goes before the arguments and so before the `=> ..` block.

The goals keep their kind tags inside the block, so `case cfc_pull.continuity => ..` works there
as it does in tactic mode, and `+deferAll .. => all_goals tac` is the conv-mode counterpart of
`cfc_pull +deferAll .. <;> tac`. The block is a `tacticSeq` and so is delimited by indentation:
a `conv` step at the enclosing level continues the block it is in, rather than being swallowed.

Going under a binder is `conv`'s job rather than the tactic's, which makes sums and the like a
two-step affair:

```lean
example : ∑ i ∈ s, star (cfc (g i) a) = cfc (∑ i ∈ s, fun x ↦ star (g i x)) a := by
  conv_lhs => enter [2, i]; cfc_pull R a
  cfc_pull R a
```

The lemmas the tactic uses are those tagged `@[cfc_pull]`; `set_option trace.Tactic.cfc_pull
true` shows which were tried and why they failed. A bracketed list adjusts that set for this one
call: `foo` adds a lemma, exactly as `@[cfc_pull]` would, and `-foo` takes one out. It goes
before the scalar ring and the element, where `simp`'s and `rw`'s lists go relative to their
location.

```lean
example (ha : 0 ≤ a) : CFC.sqrt a * CFC.sqrt a = cfc (fun x : ℂ ↦ x.sqrt * x.sqrt) a := by
  cfc_pull [CFC.sqrt_eq_cfc_complex_sqrt] ℂ a
```

That is the way to use a lemma too special — or too expensive in side goals — to be worth
tagging globally, and the way to keep a tagged lemma out of the way of the one you want. Only
declaration names may be listed: a `@[cfc_pull]` lemma is instantiated from its constant, so a
local hypothesis cannot be one, and `rw` is the way to use it. The database itself is never
modified: `-foo` says "do not use `foo` in this call".
-/
syntax (name := cfcPull) "cfc_pull"
  -- The config parser has to be `Lean.Parser.Tactic.optConfig`, not the
  -- `Lean.Parser.Term.optConfig` that `open Lean` puts in scope: only the former excludes
  -- `disch`/`discharger` from the identifiers its `valConfigItem` accepts, and so only it
  -- leaves the clause that follows to be parsed. With the other one the configuration swallows
  -- `(disch := ..)` and reports it as an unknown configuration option.
  -- the lemma list comes before the positional arguments, as `simp`'s and `rw`'s do. Both of
  -- those are optional, so with the list after them `cfc_pull [foo]` would read `[foo]` as the
  -- scalar ring rather than as a lemma list.
  Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.discharger)? (cfcPullLemmas)?
  (ppSpace colGt term:max)? (ppSpace colGt term:max)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull"
  Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.discharger)? (cfcPullLemmas)?
  (ppSpace colGt term:max)? (ppSpace colGt term:max)?
  (" => " tacticSeq)? : conv

/-- Whether the user explicitly mentioned the configuration field `field`. -/
def configMentions (stx : Syntax) (field : Name) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId == field).isSome

/-- Read the configuration, taking into account the unitality of a calculus found in the goal
when the user did not mention `unital` explicitly, and the `(disch := ..)` clause, which
`elabCFCPullConfig` cannot see. -/
def mkConfig (cfgStx : TSyntax ``Lean.Parser.Tactic.optConfig)
    (disch? : Option (TSyntax ``Lean.Parser.Tactic.discharger)) (goalUnital : Option Bool) :
    TacticM Config := do
  let mut cfg ← elabCFCPullConfig cfgStx
  if !configMentions cfgStx `unital then
    if let some u := goalUnital then
      cfg := { cfg with unital := u }
  if let some disch := disch? then
    -- the keyword is `patternIgnore`d in the parser, so it does not appear in the tree
    let `(Lean.Parser.Tactic.discharger| ($_ := $tac)) := disch | throwUnsupportedSyntax
    -- parenthesised so that a multi-tactic sequence stays one tactic
    cfg := { cfg with discharger := some (← `(tactic| ($tac))) }
  return cfg

/-- Elaborator for the `cfc_pull` tactic. -/
@[tactic cfcPull]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let `(tactic| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $[$ring?]? $[$elem?]?) := stx
    | throwUnsupportedSyntax
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem, goalUnital) ← elabRingAndElem target ring? elem?
  cfcPullTarget (← mkConfig cfg disch? goalUnital) lemmas R elem goal

/-- Elaborator for `cfc_pull` in `conv` mode. -/
@[tactic cfcPullConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let `(conv| cfc_pull $cfg:optConfig $[$disch?]? $[$lems?]? $[$ring?]? $[$elem?]?
      $[=> $tac?]?) := stx
    | throwUnsupportedSyntax
  let lhs := (← Conv.getLhs).consumeMData
  let lemmas ← elabCFCPullLemmas (← getLemmas) lems?
  let (R, elem, goalUnital) ← elabRingAndElem lhs ring? elem?
  let mut cfg ← mkConfig cfg disch? goalUnital
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
