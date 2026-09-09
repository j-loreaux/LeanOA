/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Tactic.CFCPull.Attr

/-!
# The core of the `cfc_pull` tactic

Given a scalar ring `R`, an element `a : A`, and a unitality flag (jointly called a *mode*), the
function `pull` takes an expression `e : A` and produces a function `f : R → R` together with a
proof of `e = cfc f a` (or `e = cfcₙ f a`), plus a list of side goals that the proof depends on.

## Scope and unsupported features of the `cfc_pull` tactic

* **Recursing under a binder** (`cfc_sum`, `cfc_apply_pi`) — for which there is a good workaround,
  so this may never need doing.

  **The workaround.** `conv` can go under the binder, and once there the bound variable is an
  ordinary local hypothesis and `cfc_pull` is an ordinary pull:

  ```lean
  example (ha : p a) (hg : ∀ i, ContinuousOn (g i) (spectrum R a)) :
      ∑ i ∈ s, star (cfc (g i) a) = cfc (∑ i ∈ s, fun x ↦ star (g i x)) a := by
    conv_lhs => enter [2, i]; cfc_pull R a
    cfc_pull +defer R a
  ```

  The first line pulls each summand to `cfc (fun x ↦ star (g i x)) a`; the second lets `cfc_sum`
  collect them. (`enter [2, i]`, not `ext i`: `conv` must enter `Finset.sum`'s function argument
  before it can go under the lambda.) This leaves the side goal
  `∀ i ∈ s, ContinuousOn (fun x ↦ star (g i x)) (spectrum R a)`.

  **What a built-in version would take.**

  1. *Matching.* The placeholder would have to be function-valued, `?b : ι → A`, so that the
     pattern reads `∑ i ∈ s, ?b i`. But `abstractHoles` currently uses an element metavariable.
  2. *Recursion.* `pull` would have to run under `withLocalDecl i : ι` and return a family
     `f : ι → R → R` with a pointwise proof, rather than a single function and a single
     equation. Side goals raised under the binder would have to be generalised over `i` before
     being handed back, and `Result` would have to carry the binder.

* **Compositions that also change the scalar ring.**
  `cfc_comp_re : cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A)` is a composition that changes the
  scalar ring from `ℝ` to `ℂ` on the way. The attribute now rejects lemmas like this.
  Supporting them is doable though: give `ComposeLemma` a source and a target ring
  key instead of one `ring`, index and filter `pullExisting`'s loop on the source key, and let
  the `pull newE want` that already follows every composition step do the conversion.

* **Descending through a homomorphism into another algebra.** A `pull` run fixes one algebra and
  one element for its whole duration (`Context.alg`, `Context.elem`). So `StarAlgHom.map_cfc`,
  `Unitization.complex_cfcₙ_eq_cfc_inr` and `cfc_eq_cfc_transfer` are usable only in the
  degenerate, hole-free direction: `φ (cfc f a)` is pulled towards `cfc f (φ a)`, but
  `φ (star a * a)` is not, because that needs the sub-pull `star a * a = cfc _ a` to run in the
  *domain*. Doing it in general means making the algebra and the element part of the mode and
  threading a per-node `Context`, at which point `map_cfc` becomes a `Compose`-like lemma that
  relates two different algebras. That is a substantially bigger change than the ring-changing
  composition above, and the same remark applies to `cfc_map_prod`/`cfc_map_pi`, where the
  components additionally live at *different* elements of *different* algebras.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta

/-! ### Configuration and the monad -/

/-- Configuration for the `cfc_pull` tactic. -/
structure Config where
  /-- Prefer the unital calculus when `true` (the default). -/
  unital : Bool := true
  /-- Return *unsolved* side goals to the user, instead of failing. -/
  defer : Bool := false
  /-- Return *all* side goals to the user, discharging none of them, but still deduplicate goals. -/
  deferAll : Bool := false
  /-- Unfold `let`-bound local variables (default: `false`). -/
  zetaDelta : Bool := false
  /-- A tactic to try on side goals `cfc_pull` has no built-in way to prove. -/
  discharger : Option (TSyntax `tactic) := none
  deriving Inhabited

/-- What is known about the continuous functional calculus at a given mode. -/
structure PredicateInfo where
  /-- The mode this information is about. -/
  mode : Mode
  /-- The predicate `p : A → Prop` of the calculus. -/
  pred : Expr
  /-- A proof of `p a`, created lazily on first use and shared among all lemmas requiring it. -/
  proof? : Option Expr := none
  deriving Inhabited

/-- The read-only state of a `cfc_pull` run. -/
structure Context where
  /-- The user's configuration. -/
  cfg : Config
  /-- The element `a : A` that everything is pulled towards. -/
  elem : Expr
  /-- The algebra `A`. -/
  alg : Expr
  /-- The mode requested by the user. -/
  target : Mode
  /-- The `@[cfc_pull]` database, read once at the start of the run. -/
  lemmas : Lemmas

/-- What kind of hypothesis a side goal came from. -/
inductive SideGoalKind where
  /-- The predicate `p a` of the calculus. -/
  | predicate
  /-- Continuity of a function on a spectrum. -/
  | continuity
  /-- `f 0 = 0`, required by the non-unital calculus. -/
  | mapZero
  /-- Anything else, e.g. `∀ x ∈ spectrum R a, f x ≠ 0`. -/
  | other
  deriving Inhabited, BEq, Repr

/-- Classify a side goal by its statement. -/
def SideGoalKind.ofType (type : Expr) : SideGoalKind :=
  if type.isAppOf ``IsSelfAdjoint || type.isAppOf ``IsStarNormal || isNonneg then .predicate
  else if mentions ``Continuous || mentions ``ContinuousOn then .continuity
  else if let some (_, _, rhs) := type.eq? then
    if rhs.zero? then .mapZero else .other
  else .other
where
  /-- Whether the constant `n` occurs anywhere in the statement. -/
  mentions (n : Name) : Bool := (type.find? (·.isConstOf n)).isSome
  /-- Whether the statement is `0 ≤ _`, the predicate of the calculus over `ℝ≥0`. -/
  isNonneg : Bool := match type.le? with
    | some (_, lhs, _) => lhs.zero?
    | none => false

/-- The name a deferred goal of this kind is given. -/
def SideGoalKind.tag : SideGoalKind → Name
  | .predicate => `cfc_pull.predicate
  | .continuity => `cfc_pull.continuity
  | .mapZero => `cfc_pull.mapZero
  | .other => `cfc_pull.side

/-- The mutable state of a `cfc_pull` run; consists of an array of side goals and the predicate
information for the relevant functional calculi. -/
structure State where
  /-- Side goals that must be discharged, each paired with the kind of hypothesis it came from. -/
  sideGoals : Array (MVarId × SideGoalKind) := #[]
  /-- Cached information about the calculus at each mode encountered so far. -/
  predicates : Array PredicateInfo := #[]

/-- The monad in which `cfc_pull` runs. -/
abbrev PullM := ReaderT Context <| StateRefT State MetaM

/-- The outcome of pulling a single expression. -/
structure Result where
  /-- The application `cfc f a` to which the expression was rewritten. -/
  app : CFCApp
  /-- A proof of `e = app.toExpr`, where `e` is the expression that was pulled. -/
  proof : Expr
  deriving Inhabited

instance : ExceptToTraceResult Exception Result where
  toTraceResult
    | .error _ => .error
    | .ok _ => .success

/-! ### Small utilities -/

/-- Everything a failed candidate must not leave behind: the `MetaM` state, and the side goals
and predicate cache the attempt accumulated. -/
structure SavedState where
  /-- The ambient `MetaM` state. -/
  metaState : Meta.SavedState
  /-- The state of the `cfc_pull` run. -/
  pullState : State

instance : MonadBacktrack SavedState PullM where
  saveState := return { metaState := ← Meta.saveState, pullState := ← get }
  restoreState s := do s.metaState.restore; set s.pullState

/-- The outcome of one attempt: what it produced, or why it did not apply. -/
abbrev Attempt := Except MessageData Result

/-- A candidate that does not apply is the routine outcome of trying it, not an exception
escaping, so it reads as a trace failure (`❌️`) rather than as an error (`💥️`). -/
instance : ExceptToTraceResult Exception Attempt where
  toTraceResult
    | .error _ => .error
    | .ok (.error _) => .failure
    | .ok (.ok _) => .success

/-- Run `x` under a trace node headed by `header`, which on failure also reports why. Every
message raised inside is read against that header, so none of them needs to repeat what is being
tried.

This is the form for a step the tactic has committed to, where failure is a real error (`💥️`)
rather than a candidate declining to apply; `attempt?` is the backtracking form. -/
def withAttempt (header : MessageData) (x : PullM Result) : PullM Result :=
  withTraceNode `Tactic.cfc_pull
    (fun
      | .error ex => return m!"{header}: {ex.toMessageData}"
      | .ok _ => return header) x

/-- `withAttempt`, reverting the metavariable context and the state of the run when the attempt
fails, so that the next candidate starts from a clean slate. -/
def attempt? (header : MessageData) (x : PullM Result) : PullM (Option Result) := do
  let attempt ← withTraceNode `Tactic.cfc_pull
    (fun (r : Except Exception Attempt) => return match r with
      | .ok (.error reason) => m!"{header}: {reason}"
      | .error ex => m!"{header}: {ex.toMessageData}"
      | .ok (.ok _) => header) do
    let s ← saveState
    try
      return .ok (← x)
    catch ex =>
      restoreState s
      return .error ex.toMessageData
  return attempt.toOption

/-- Strip an `autoParam` wrapper, so that a deferred goal displays as the user expects. -/
def stripAutoParam (e : Expr) : Expr :=
  if e.isAutoParam then e.appFn!.appArg! else e

/-- Register a new side goal of the given type, named after its kind. -/
def newSideGoal (type : Expr) (kind : SideGoalKind) : PullM Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar type (tag := kind.tag)
  modify fun s => { s with sideGoals := s.sideGoals.push (g.mvarId!, kind) }
  return g

/-- Only used to build the expression `ContinuousFunctionalCalculus R A p` with instance arguments
synthesized (or the non-unital variant). If `p` was the last argument, we could use `mkAppM`. -/
def mkClassApp (clsName : Name) (args : Array Expr) : MetaM Expr := do
  let arity := (← getConstInfo clsName).type.getForallArity
  mkAppOptM clsName (args.map some ++ Array.replicate (arity - args.size) none)

/-- The index in the cache of the information about the calculus at `mode`, if known. -/
def findPredicateIdx (mode : Mode) : PullM (Option Nat) := do
  for (pi, i) in (← get).predicates.zipIdx do
    if pi.mode.unital == mode.unital && (← withReducible <| isDefEq pi.mode.ring mode.ring) then
      return some i
  return none

/-- Determine the predicate `p : A → Prop` associated to `mode` by synthesising the instance and
reading its `outParam`. Fails if there is no such calculus. -/
def getPredicate (mode : Mode) : PullM Expr := do
  if let some i ← findPredicateIdx mode then
    return (← get).predicates[i]!.pred
  let ctx ← read
  let p ← mkFreshExprMVar (← mkArrow ctx.alg (.sort .zero))
  let clsName :=
    if mode.unital then ``ContinuousFunctionalCalculus else ``NonUnitalContinuousFunctionalCalculus
  let noCalculus {α : Type} : PullM α :=
    throwError "`cfc_pull`: `{ctx.alg}` has no {if mode.unital then "" else "non-unital "}\
      continuous functional calculus over `{mode.ring}`"
  let cls ← try mkClassApp clsName #[mode.ring, ctx.alg, p] catch _ => noCalculus
  try
    discard <| synthInstance cls
  catch _ => noCalculus
  let pred ← instantiateMVars p
  if pred.hasExprMVar then
    throwError "`cfc_pull` could not determine the predicate associated to {mode}"
  trace[Tactic.cfc_pull] "predicate for {mode} is {pred}"
  modify fun s => { s with predicates := s.predicates.push { mode, pred } }
  return pred

/-- A proof of `p a` for the calculus at `mode`. The metavariable is created on first use and
then shared, so a run leaves at most one predicate side goal per mode. -/
def getPredicateProof (mode : Mode) : PullM Expr := do
  let _ ← getPredicate mode
  let some i ← findPredicateIdx mode | throwError "internal error: missing predicate cache entry"
  let pi := (← get).predicates[i]!
  if let some prf := pi.proof? then return prf
  let prf ← newSideGoal (mkApp pi.pred (← read).elem) .predicate
  modify fun s => { s with predicates := s.predicates.set! i { pi with proof? := some prf } }
  return prf

/-- Deal with the hypotheses of an instantiated lemma: those that are the predicate `p a` at
`mode` are filled with the shared proof, the rest become side goals. -/
def collectHypotheses (mvars : Array Expr) (bis : Array BinderInfo) (mode : Mode) :
    PullM Unit := do
  let ctx ← read
  for (mvar, bi) in mvars.zip bis do
    let mvarId := mvar.mvarId!
    if ← mvarId.isAssigned then continue
    if bi.isInstImplicit then continue
    let type := stripAutoParam (← instantiateMVars (← mvarId.getType))
    unless ← isProp type do
      throwError "the argument of type `{type}` could not be determined"
    let pred ← getPredicate mode
    if ← withReducible <| isDefEq type (mkApp pred ctx.elem) then
      mvarId.assign (← getPredicateProof mode)
      trace[Tactic.cfc_pull] "filled `{type}` from the shared predicate proof"
    else
      /- `p b` for an element `b` other than `a` — the inner element of a composition, say — is a
      predicate goal too, but `SideGoalKind.ofType` sees only the statement and so cannot
      recognize one whose predicate is a variable.  The outer metavariables are frozen: this is a
      test, and only `b` is allowed to be determined by it. -/
      let kind ← withNewMCtxDepth do
        let b ← mkFreshExprMVar ctx.alg
        if ← withReducible <| isDefEq type (mkApp pred b) then pure .predicate
        else pure (.ofType type)
      mvarId.assign (← newSideGoal type kind)
      trace[Tactic.cfc_pull] "deferred `{type}`"

/-! ### The scalar conversion graph -/

/-- Whether a result obtained at ring key `src` is already usable at `tgt`. -/
def RingKey.isUsableAt (src tgt : RingKey) : Bool :=
  src == .any || src == tgt

/-- A shortest sequence of tagged `Scalar` lemmas converting a `cfc[ₙ]` over `src` into one over
`tgt`, or `none` if there is no such sequence. In practice this array only has length 1 or 2. -/
def scalarPath (src tgt : RingKey) (unital : Bool) : PullM (Option (Array ScalarLemma)) := do
  if src.isUsableAt tgt then return some #[]
  let edges := (← read).lemmas.scalar.filter (·.unital == unital)
  -- breadth-first search; the graph has a handful of nodes, so this is cheap
  let mut frontier : Array (RingKey × Array ScalarLemma) := #[(src, #[])]
  let mut seen : Array RingKey := #[src]
  for _ in [0:edges.size + 1] do
    let mut next := #[]
    for (node, path) in frontier do
      for e in edges do
        unless e.src.isUsableAt node do continue
        if seen.contains e.tgt then continue
        let path := path.push e
        if e.tgt.isUsableAt tgt then return some path
        seen := seen.push e.tgt
        next := next.push (e.tgt, path)
    if next.isEmpty then return none
    frontier := next
  return none

/-! ### Applying tagged lemmas -/

/-- Rewrite `e` with a tagged equation between two applications of the calculus, by matching one
side against `e` and returning the other, instantiated. This handles the `Scalar`, `Unital` and
`Compose` categories. -/
def rewriteWithCFCLemma (declName : Name) (srcOnLhs : Bool) (e : Expr) (mode : Mode) :
    PullM (CFCApp × Expr) := do
  let ctx ← read
  let (mvars, bis, lhs, rhs, proof) ← instantiateLemma declName
  let (srcSide, tgtSide) := if srcOnLhs then (lhs, rhs) else (rhs, lhs)
  let some cs := CFCApp.match? srcSide |
    throwError "not a `cfc`-to-`cfc` lemma"
  unless ← withReducible <| isDefEq cs.alg ctx.alg do
    throwError "wrong algebra"
  unless ← withReducible <| isDefEq cs.pred (← getPredicate mode) do
    throwError "wrong predicate"
  unless ← withReducible <| isDefEq srcSide e do
    throwError "does not match `{e}`"
  synthAppInstances declName default mvars bis false false
  let tgtSide ← instantiateMVars tgtSide
  let some ct := CFCApp.match? tgtSide |
    throwError "not a `cfc`-to-`cfc` lemma"
  let newApp := ct.withFn (← Core.betaReduce ct.fn)
  let step ← if srcOnLhs then pure proof else mkEqSymm proof
  let step ← mkExpectedTypeHint step (← mkEq e newApp.toExpr)
  collectHypotheses mvars bis mode
  return (newApp, step)

/-- Apply a transition lemma (a `Scalar` or `Unital` lemma) to a result. -/
def applyTransition (declName : Name) (srcOnLhs : Bool) (res : Result) : PullM Result := do
  let (app, step) ← rewriteWithCFCLemma declName srcOnLhs res.app.toExpr res.app.toMode
  return { app, proof := ← mkEqTrans res.proof step }

/-- Change the mode: unitality first to avoid goals of the form `?f 0 = 0`, then the scalar ring. -/
def convert (res : Result) (want : Mode) : PullM Result := do
  let mut res := res
  if res.app.unital != want.unital then
    let mut done := false
    for l in (← read).lemmas.unital do
      unless ← l.ring.matchesRing res.app.ring do continue
      -- to reach the unital calculus we start from the non-unital side, and conversely
      let srcOnLhs := if want.unital then l.nonUnitalOnLhs else !l.nonUnitalOnLhs
      if let some r ← attempt? (ppConst l.declName) (applyTransition l.declName srcOnLhs res) then
        res := r; done := true; break
    unless done do
      throwError "`cfc_pull` could not convert {res.app.toMode} into {want}"
  unless ← withReducible <| isDefEq res.app.ring want.ring do
    let some path ← scalarPath (.ofExpr res.app.ring) (.ofExpr want.ring) want.unital
      | throwError "`cfc_pull` has no way to convert a {res.app.toMode} into a {want}"
    for l in path do
      res ← withAttempt (ppConst l.declName) (applyTransition l.declName true res)
    unless ← withReducible <| isDefEq res.app.ring want.ring do
      throwError "`cfc_pull` converted to {res.app.toMode}, but {want} was requested"
  return res

/-- Apply a `Pull` lemma to `e`, recursing on the holes with `rec`.

The steps, in order: fix the algebra, ring, predicate and element of the lemma; replace the holes
of its algebraic side by fresh metavariables and match the result against `e`; recurse on what
the holes matched; assign the functions so obtained; synthesise instances; and assemble the
proof. Assigning the element *before* matching is what makes lemmas whose algebraic side does
not mention it (such as `cfc_const_one`) apply only at the right element. -/
def applyPullLemma (l : PullLemma) (e : Expr) (want : Mode)
    (rec : Expr → Mode → PullM Result) : PullM Result := do
  let ctx ← read
  let (mvars, bis, lhs, rhs, proof) ← instantiateLemma l.declName
  let (cfcSide, algSide) := if l.cfcOnLhs then (lhs, rhs) else (rhs, lhs)
  let some c := CFCApp.match? cfcSide | throwError "not a pull lemma"
  unless ← withReducible <| isDefEq c.alg ctx.alg do
    throwError "wrong algebra"
  if l.ring == .any then
    unless ← withReducible <| isDefEq c.ring want.ring do
      throwError "wrong scalar ring"
  let mode : Mode := { c.toMode with ring := ← instantiateMVars c.ring }
  unless ← withReducible <| isDefEq c.pred (← getPredicate mode) do
    throwError "wrong predicate"
  unless ← withReducible <| isDefEq c.elem ctx.elem do
    throwError "wrong element"
  -- Replace the holes by fresh metavariables and match.  `pat` is kept unassigned so that the
  -- holes can be abstracted again below, after unification has filled in everything else.
  let (pat, holes, phs) ←
    abstractHoles (isHoleFor c (fun e => return e.isMVar && !(← e.mvarId!.isAssigned)))
      (mkFreshExprMVar ctx.alg) algSide
  unless ← withReducible <| isDefEq pat e do
    throwError "does not match: `{pat}` ≠ `{e}`"
  -- Recurse on the subterms the holes matched.
  let mut results := #[]
  for h in phs do
    let sub ← instantiateMVars h
    if sub.isMVar then
      throwError "the hole `{h}` was not determined by matching"
    results := results.push (← rec sub mode)
  for (hole, res) in holes.zip results do
    let some hc := CFCApp.match? hole | throwError "internal error: bad hole"
    unless ← withReducible <| isDefEq hc.fn res.app.fn do
      throwError "could not use the function found for `{hole}`"
  synthAppInstances l.declName default mvars bis false false
  -- Assemble the proof.  `e = ⟨algebraic side⟩` by congruence, then the lemma itself.
  let algSide' ← instantiateMVars algSide
  let cfcSide' ← instantiateMVars cfcSide
  let some cc := CFCApp.match? cfcSide' | throwError "internal error: lost the `cfc` side"
  let newApp := cc.withFn (← Core.betaReduce cc.fn)
  let hcongr ← withLocalDeclsD (phs.map fun _ => (`x, fun _ => pure ctx.alg)) fun xs => do
    let body ← instantiateMVars <| pat.replace fun s => match s with
      | .mvar m => (phs.findIdx? (·.mvarId! == m)).map (xs[·]!)
      | _ => none
    let F ← mkLambdaFVars xs body
    (results.map (·.proof)).foldlM (init := ← mkEqRefl F) fun h h' => mkCongr h h'
  let hcongr ← mkExpectedTypeHint hcongr (← mkEq e algSide')
  let lemProof ← if l.cfcOnLhs then mkEqSymm proof else pure proof
  let total ← mkEqTrans hcongr lemProof
  let total ← mkExpectedTypeHint total (← mkEq e newApp.toExpr)
  collectHypotheses mvars bis mode
  return { app := newApp, proof := total }

/-- Apply a hole-free `Pull` lemma *without* insisting that its element be the one we are pulling
towards: `e` is rewritten to `cfc F b` for whatever element `b` the lemma matches. The caller
then re-enters `pull`, which turns the mismatch into a composition.

This is what lets `NormedSpace.exp (I • a)` become `cfc Complex.exp (I • a)` and from there
`cfc (fun x ↦ Complex.exp (I * x)) a`. Only hole-free lemmas are eligible, because the holes of a
lemma applied at an unknown element would themselves be applications of the calculus at that
unknown element. -/
def applyLooseLemma (l : PullLemma) (e : Expr) (want : Mode) : PullM (Expr × Expr) := do
  let ctx ← read
  if l.numHoles != 0 then
    throwError "it has holes, so it cannot be applied at an unknown element"
  let (mvars, bis, lhs, rhs, proof) ← instantiateLemma l.declName
  let (cfcSide, algSide) := if l.cfcOnLhs then (lhs, rhs) else (rhs, lhs)
  let some c := CFCApp.match? cfcSide | throwError "not a pull lemma"
  unless ← withReducible <| isDefEq c.alg ctx.alg do
    throwError "wrong algebra"
  if l.ring == .any then
    unless ← withReducible <| isDefEq c.ring want.ring do
      throwError "wrong scalar ring"
  let mode : Mode := { c.toMode with ring := ← instantiateMVars c.ring }
  unless ← withReducible <| isDefEq c.pred (← getPredicate mode) do
    throwError "wrong predicate"
  unless ← withReducible <| isDefEq algSide e do
    throwError "does not match `{e}`"
  synthAppInstances l.declName default mvars bis false false
  let cfcSide ← instantiateMVars cfcSide
  let some cc := CFCApp.match? cfcSide | throwError "internal error: lost the `cfc` side"
  let newE := (cc.withFn (← Core.betaReduce cc.fn)).toExpr
  if newE == e then throwError "made no progress"
  let step ← if l.cfcOnLhs then mkEqSymm proof else pure proof
  let step ← mkExpectedTypeHint step (← mkEq e newE)
  collectHypotheses mvars bis mode
  return (newE, step)

/-- Convert an `IdLemma` into the `PullLemma` that `applyPullLemma` expects. -/
def IdLemma.toPullLemma (l : IdLemma) : PullLemma where
  declName := l.declName
  prio := 1000
  ring := l.ring
  unital := l.unital
  cfcOnLhs := l.cfcOnLhs
  numHoles := 0

/-! ### Ordering candidate lemmas -/

/-- How far a `Pull` lemma is from applying given mode: used by `pullCandidates` to sort lemmas. -/
structure Cost where
  /-- The number of `Scalar` lemmas needed to jump from one mode to the other. -/
  conversions : Nat
  /-- Whether a change of unitality is needed on top of that. -/
  changesUnitality : Bool
  /-- The priority associated to a `cfc_pull` lemma; higher is better. -/
  prio : Nat
  /-- The number of holes on the lemma's algebraic side; fewer is better. -/
  holes : Nat
  deriving Inhabited, Repr

instance : Ord Cost where
  compare a b :=
    compare a.conversions b.conversions
      |>.then (compare a.changesUnitality b.changesUnitality)
      |>.then (compare b.prio a.prio)
      |>.then (compare a.holes b.holes)

/-- The `Pull` lemmas that could apply to `e`, best first, ordered by `Cost`. -/
partial def pullCandidates (e : Expr) (want : Mode) : PullM (Array PullLemma) := do
  let ctx ← read
  let cands ← ctx.lemmas.pull.getMatch e
  let wantKey := RingKey.ofExpr want.ring
  let mut scored : Array (Cost × PullLemma) := #[]
  for l in cands do
    -- `none` here means the lemma's ring is unreachable, not that it is expensive.
    let conversions? ←
      if l.ring.isUsableAt wantKey then pure (some 0)
      else pure ((← scalarPath l.ring wantKey want.unital).map (·.size))
    match conversions? with
    | none =>
      trace[Tactic.cfc_pull]
        "skipping `{ppConst l.declName}`: no conversion from {l.ring} to {wantKey}"
    | some conversions =>
      scored := scored.push
        ({ conversions, changesUnitality := l.unital != want.unital, prio := l.prio,
            holes := l.numHoles }, l)
  return (scored.qsort fun a b => compare a.1 b.1 |>.isLT).map (·.2)

/-! ### The recursion -/

mutual

/-- Pull `e` towards `cfc f a` at the mode `want`. -/
partial def pull (e : Expr) (want : Mode) : PullM Result := withIncRecDepth do
  withTraceNode `Tactic.cfc_pull (fun _ => return m!"pull {e} into a {want}") do
    let ctx ← read
    -- 1. the element itself
    if ← withReducible <| isDefEq e ctx.elem then
      for l in ctx.lemmas.id do
        let r ← attempt? (ppConst l.declName) do
          convert (← applyPullLemma l.toPullLemma e want pull) want
        if let some r := r then return r
    -- 2. an application of the calculus
    if let some c := CFCApp.match? e then
      let r ← attempt? m!"the calculus already applied at {c.elem}" do
        convert (← pullExisting c want) want
      if let some r := r then return r
    -- 3. tagged pull lemmas
    let candidates ← pullCandidates e want
    trace[Tactic.cfc_pull] "candidates: {candidates.map (ppConst ·.declName)}"
    for l in candidates do
      let r ← attempt? (ppConst l.declName) do convert (← applyPullLemma l e want pull) want
      if let some r := r then return r
    -- 3b. tagged pull lemmas applied at some *other* element, followed by a composition
    for l in candidates do
      if l.numHoles != 0 then continue
      let r ← attempt? (ppConst l.declName) do
        let (newE, step) ← applyLooseLemma l e want
        let res ← pull newE want
        return { res with proof := ← mkEqTrans step res.proof }
      if let some r := r then return r
    let head := match e.getAppFn.constName? with
      | some n => ppConst n
      | none => m!"_"
    let mut msg := m!"`cfc_pull` got stuck on `{e}`{indentD m!"(head symbol: \
      {head}, target: {want} at `{ctx.elem}`)"}"
    -- A local definition is an atom unless `+zetaDelta` is given.
    if !ctx.cfg.zetaDelta then
      if let .fvar fvarId := e.getAppFn then
        if (← fvarId.getDecl).isLet then
          msg := msg ++ m!"\n`{e.getAppFn}` is a local definition, and `cfc_pull` does not look\n\
            at what it stands for. Unfold it with `cfc_pull +zetaDelta ..`, or rewrite it away\n\
            first — `set .. with h` hands you the equation `h` to do it with."
    -- `e` is already an application of the calculus, just to the wrong element; this is a dead end.
    if let some c := CFCApp.match? e then
      unless ← withNewMCtxDepth <| withReducible <| isDefEq c.elem ctx.elem do
        msg := msg ++ m!"\nThe calculus is already applied here, but to a different\n\
          element; `cfc_pull` only ever makes the element simpler, never more\n\
          complicated. If it is that element you meant to pull towards, name\n\
          it:{indentD m!"cfc_pull {want.ring} {c.elem}"}"
    throwError msg

/-- Handle `e = cfc g b`: either we pull towards `b`, or this is a composition. -/
partial def pullExisting (c : CFCApp) (want : Mode) : PullM Result := do
  let ctx ← read
  let e := c.toExpr
  let mode := c.toMode
  if ← withReducible <| isDefEq c.elem ctx.elem then
    return { app := c, proof := ← mkEqRefl e }
  -- The calculus is applied to something else, so this is a composition. Adjust unitality first.
  if c.unital != want.unital then
    for l in ctx.lemmas.unital do
      unless ← l.ring.matchesRing c.ring do continue
      let srcOnLhs := if want.unital then l.nonUnitalOnLhs else !l.nonUnitalOnLhs
      let r ← attempt? (ppConst l.declName) do
        let (newApp, step) ← rewriteWithCFCLemma l.declName srcOnLhs e mode
        let res ← pull newApp.toExpr want
        return { res with proof := ← mkEqTrans step res.proof }
      if let some r := r then return r
  -- Look for a tagged composition lemma matching the head of the inner element.
  let innerHead := c.elem.getAppFn.constName?
  for l in ctx.lemmas.compose do
    unless l.unital == c.unital do continue
    unless ← l.ring.matchesRing c.ring do continue
    unless some l.innerHead == innerHead do continue
    let r ← attempt? (ppConst l.declName) do
      let (newApp, step) ← rewriteWithCFCLemma l.declName l.srcOnLhs e mode
      let res ← pull newApp.toExpr want
      return { res with proof := ← mkEqTrans step res.proof }
    if let some r := r then return r
  -- Otherwise, pull the inner element first and try again; that turns `cfc g b` into
  -- `cfc g (cfc h a)`, which the composition lemma for `cfc` (namely `cfc_comp'`) handles.
  let inner ← pull c.elem mode
  if inner.app.toExpr == c.elem then
    throwError "`cfc_pull` made no progress on the inner element `{c.elem}`"
  let newE := (c.withElem inner.app.toExpr).toExpr
  let step ← withLocalDeclD `y ctx.alg fun y => do
    let F ← mkLambdaFVars #[y] (c.withElem y).toExpr
    mkCongrArg F inner.proof
  let step ← mkExpectedTypeHint step (← mkEq e newE)
  let res ← pull newE want
  return { res with proof := ← mkEqTrans step res.proof }

end

/-! ### Entry point -/

/-- Determine the mode to work in from information supplied by the user. -/
def mkMode (cfg : Config) (R alg : Expr) : MetaM Mode := do
  if cfg.unital then
    let ok ←
      try
        let p ← mkFreshExprMVar (← mkArrow alg (.sort .zero))
        let cls ← mkClassApp ``ContinuousFunctionalCalculus #[R, alg, p]
        pure (← trySynthInstance cls).toOption.isSome
      catch _ => pure false
    if ok then return { ring := R, unital := true }
  return { ring := R, unital := false }

/-- Run the core of `cfc_pull` on `e`: returns the rewritten expression, a proof that `e` equals
it, and the side goals that proof depends on. -/
def runPull (cfg : Config) (lemmas : Lemmas) (R elem e : Expr) :
    MetaM (Expr × Expr × Array (MVarId × SideGoalKind)) := do
  let e := e.consumeMData
  let alg ← inferType elem
  unless ← isDefEq (← inferType e) alg do
    throwError "`cfc_pull`: `{e}` does not live in the algebra `{alg}`"
  let target ← mkMode cfg R alg
  let ctx : Context := { cfg, elem, alg, target, lemmas }
  let (res, st) ←
    withConfig (fun c => { c with zetaDelta := cfg.zetaDelta }) <|
      ((do let _ ← getPredicate target; pull e target).run ctx).run {}
  let goals ← st.sideGoals.filterM fun (g, _) => return !(← g.isAssigned)
  return (← instantiateMVars res.app.toExpr, ← instantiateMVars res.proof, goals)

end Mathlib.Tactic.CFCPull
