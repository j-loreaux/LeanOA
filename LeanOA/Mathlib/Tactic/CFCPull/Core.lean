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
  /-- The maximum recursion depth. -/
  maxDepth : Nat := 48
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
  /-- The current recursion depth. -/
  depth : Nat := 0

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

/-- The mutable state of a `cfc_pull` run. -/
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

/-- Exception used by the recursion-depth guard. -/
initialize maxDepthExceptionId : InternalExceptionId ←
  registerInternalExceptionId `Mathlib.Tactic.CFCPull.maxDepth

/-- Run `x`, reverting metavariable context and `PullM` state upon failure. -/
def observing? {α : Type} (x : PullM α) : PullM (Option α) := do
  let mctx ← getMCtx
  let s ← get
  try
    return some (← x)
  catch ex =>
    -- if the exception is for max recursion depth, rethrow it, otherwise revert state and trace it.
    if let .internal id _ := ex then
      if id == maxDepthExceptionId then throw ex
    setMCtx mctx
    set s
    trace[Tactic.cfc_pull] "{crossEmoji} {ex.toMessageData}"
    return none

/-- Increase the recursion depth, failing if the configured maximum is reached. -/
def withIncDepth {α : Type} (x : PullM α) : PullM α := do
  let ctx ← read
  if ctx.depth ≥ ctx.cfg.maxDepth then
    throw (.internal maxDepthExceptionId)
  withReader (fun c => { c with depth := c.depth + 1 }) x

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

/-- Synthesise every instance-implicit argument of an instantiated lemma that is still
unassigned. Failure here is the mechanism by which lemmas are restricted to the rings and
algebras they apply to, so failures must propagate: hence `allowSynthFailures := false`. -/
def synthesizeInstances (declName : Name) (mvars : Array Expr) (bis : Array BinderInfo) :
    MetaM Unit := do
  try
    synthAppInstances declName default mvars bis false false
  catch ex =>
    throwError "`{ppConst declName}` does not apply here: {ex.toMessageData}"

/-- Deal with the hypotheses of an instantiated lemma: those that are the predicate `p a` at
`mode` are filled with the shared proof, the rest become side goals. -/
def collectHypotheses (declName : Name) (mvars : Array Expr) (bis : Array BinderInfo)
    (mode : Mode) : PullM Unit := do
  let ctx ← read
  for (mvar, bi) in mvars.zip bis do
    let mvarId := mvar.mvarId!
    if ← mvarId.isAssigned then continue
    if bi.isInstImplicit then continue
    let type := stripAutoParam (← instantiateMVars (← mvarId.getType))
    unless ← isProp type do
      throwError "`{ppConst declName}` does not apply here: the argument of type \
        `{type}` could not be determined"
    let pred ← getPredicate mode
    if ← withReducible <| isDefEq type (mkApp pred ctx.elem) then
      mvarId.assign (← getPredicateProof mode)
      trace[Tactic.cfc_pull]
        "`{ppConst declName}`: filled `{type}` from the shared predicate proof"
    else
      mvarId.assign (← newSideGoal type (.ofType type))
      trace[Tactic.cfc_pull] "`{ppConst declName}`: deferred `{type}`"

/-- Test whether an expression is an unassigned metavariable, i.e. a variable of the lemma being
applied. -/
def isLemmaVar : Expr → MetaM Bool
  | .mvar m => return !(← m.isAssigned)
  | _ => return false

/-! ### The scalar conversion graph -/

/-- Whether a result obtained at ring key `src` is already usable at `tgt`. A lemma polymorphic
in its scalar ring (`RingKey.any`) is instantiated directly at the target ring, so no conversion
is needed. -/
def RingKey.isUsableAt (src tgt : RingKey) : Bool :=
  src == .any || src == tgt

/-- A shortest sequence of tagged `Scalar` lemmas converting a `cfc[ₙ]` over `src` into one over
`tgt`, or `none` if there is no such sequence. -/
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
side against `e` and returning the other, instantiated.

This single routine covers the `Scalar`, `Unital` and `Compose` categories: they differ only in
which of the ring, the unitality and the element the two sides disagree about, and none of that
matters here — matching against `e` determines everything. `mode` is the mode of `e`, which is
used to fill the predicate hypotheses of the lemma. -/
def rewriteWithCFCLemma (declName : Name) (srcOnLhs : Bool) (e : Expr) (mode : Mode) :
    PullM (CFCApp × Expr) := do
  let ctx ← read
  let (mvars, bis, lhs, rhs, proof) ← instantiateLemma declName
  let (srcSide, tgtSide) := if srcOnLhs then (lhs, rhs) else (rhs, lhs)
  let some cs := CFCApp.match? srcSide |
    throwError "`{ppConst declName}` is not a `cfc`-to-`cfc` lemma"
  -- Everything that decides whether this lemma applies *here* is a match against the user's
  -- expression, so it runs at reducible transparency. `synthesizeInstances` below is the
  -- exception; see the note on transparency in the module docstring.
  unless ← withReducible <| isDefEq cs.alg ctx.alg do
    throwError "`{ppConst declName}`: wrong algebra"
  unless ← withReducible <| isDefEq cs.pred (← getPredicate mode) do
    throwError "`{ppConst declName}`: wrong predicate"
  unless ← withReducible <| isDefEq srcSide e do
    throwError "`{ppConst declName}` does not match `{e}`"
  synthesizeInstances declName mvars bis
  let tgtSide ← instantiateMVars tgtSide
  let some ct := CFCApp.match? tgtSide |
    throwError "`{ppConst declName}` is not a `cfc`-to-`cfc` lemma"
  let newApp := ct.withFn (← Core.betaReduce ct.fn)
  let step ← if srcOnLhs then pure proof else mkEqSymm proof
  let step ← mkExpectedTypeHint step (← mkEq e newApp.toExpr)
  collectHypotheses declName mvars bis mode
  return (newApp, step)

/-- Apply a transition lemma (a `Scalar` or `Unital` lemma) to a result. -/
def applyTransition (declName : Name) (srcOnLhs : Bool) (res : Result) : PullM Result := do
  let (app, step) ← rewriteWithCFCLemma declName srcOnLhs res.app.toExpr res.app.toMode
  return { app, proof := ← mkEqTrans res.proof step }

/-- Convert a result to the requested mode: first the unitality, then the scalar ring.

Doing the unitality first keeps the `f 0 = 0` side goal of `cfcₙ_eq_cfc` about the smallest
possible function, and implements the rule that a `cfcₙ` at the right element should become a
`cfc` immediately when the unital calculus was requested. -/
def convert (res : Result) (want : Mode) : PullM Result := do
  let mut res := res
  if res.app.unital != want.unital then
    let mut done := false
    for l in (← read).lemmas.unital do
      unless ← l.ring.matchesRing res.app.ring do continue
      -- to reach the unital calculus we start from the non-unital side, and conversely
      let srcOnLhs := if want.unital then l.nonUnitalOnLhs else !l.nonUnitalOnLhs
      if let some r ← observing? (applyTransition l.declName srcOnLhs res) then
        res := r; done := true; break
    unless done do
      throwError "`cfc_pull` could not convert {res.app.toMode} into {want}"
  unless ← withReducible <| isDefEq res.app.ring want.ring do
    let some path ← scalarPath (.ofExpr res.app.ring) (.ofExpr want.ring) want.unital
      | throwError "`cfc_pull` has no way to convert a {res.app.toMode} into a {want}"
    for l in path do
      res ← applyTransition l.declName true res
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
  let some c := CFCApp.match? cfcSide | throwError "`{ppConst l.declName}` is not a pull lemma"
  unless ← withReducible <| isDefEq c.alg ctx.alg do
    throwError "`{ppConst l.declName}`: wrong algebra"
  if l.ring == .any then
    unless ← withReducible <| isDefEq c.ring want.ring do
      throwError "`{ppConst l.declName}`: wrong scalar ring"
  let mode : Mode := { c.toMode with ring := ← instantiateMVars c.ring }
  unless ← withReducible <| isDefEq c.pred (← getPredicate mode) do
    throwError "`{ppConst l.declName}`: wrong predicate"
  unless ← withReducible <| isDefEq c.elem ctx.elem do
    throwError "`{ppConst l.declName}`: wrong element"
  -- Replace the holes by fresh metavariables and match.  `pat` is kept unassigned so that the
  -- holes can be abstracted again below, after unification has filled in everything else.
  let (pat, holes, phs) ←
    abstractHoles (isHoleFor c isLemmaVar) (mkFreshExprMVar ctx.alg) algSide
  unless ← withReducible <| isDefEq pat e do
    throwError "`{ppConst l.declName}` does not match: `{pat}` ≠ `{e}`"
  -- Recurse on the subterms the holes matched.
  let mut results := #[]
  for h in phs do
    let sub ← instantiateMVars h
    if sub.isMVar then
      throwError "`{ppConst l.declName}`: the hole `{h}` was not determined by matching"
    results := results.push (← rec sub mode)
  for (hole, res) in holes.zip results do
    let some hc := CFCApp.match? hole | throwError "internal error: bad hole"
    unless ← withReducible <| isDefEq hc.fn res.app.fn do
      throwError "`{ppConst l.declName}`: could not use the function found for `{hole}`"
  synthesizeInstances l.declName mvars bis
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
    -- `mkCongr` one hole at a time: from `hᵢ : xᵢ = yᵢ`, folding it over `rfl : F = F` gives
    -- `F x₀ ⋯ xₙ = F y₀ ⋯ yₙ`. `F` is non-dependent by construction.
    (results.map (·.proof)).foldlM (init := ← mkEqRefl F) fun h h' => mkCongr h h'
  let hcongr ← mkExpectedTypeHint hcongr (← mkEq e algSide')
  let lemProof ← if l.cfcOnLhs then mkEqSymm proof else pure proof
  let total ← mkEqTrans hcongr lemProof
  let total ← mkExpectedTypeHint total (← mkEq e newApp.toExpr)
  collectHypotheses l.declName mvars bis mode
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
    throwError "`{ppConst l.declName}` has holes, so it cannot be applied at an unknown \
      element"
  let (mvars, bis, lhs, rhs, proof) ← instantiateLemma l.declName
  let (cfcSide, algSide) := if l.cfcOnLhs then (lhs, rhs) else (rhs, lhs)
  let some c := CFCApp.match? cfcSide | throwError "`{ppConst l.declName}` is not a pull lemma"
  unless ← withReducible <| isDefEq c.alg ctx.alg do
    throwError "`{ppConst l.declName}`: wrong algebra"
  if l.ring == .any then
    unless ← withReducible <| isDefEq c.ring want.ring do
      throwError "`{ppConst l.declName}`: wrong scalar ring"
  let mode : Mode := { c.toMode with ring := ← instantiateMVars c.ring }
  unless ← withReducible <| isDefEq c.pred (← getPredicate mode) do
    throwError "`{ppConst l.declName}`: wrong predicate"
  unless ← withReducible <| isDefEq algSide e do
    throwError "`{ppConst l.declName}` does not match `{e}`"
  synthesizeInstances l.declName mvars bis
  let cfcSide ← instantiateMVars cfcSide
  let some cc := CFCApp.match? cfcSide | throwError "internal error: lost the `cfc` side"
  let newE := (cc.withFn (← Core.betaReduce cc.fn)).toExpr
  if newE == e then throwError "`{ppConst l.declName}` made no progress"
  let step ← if l.cfcOnLhs then mkEqSymm proof else pure proof
  let step ← mkExpectedTypeHint step (← mkEq e newE)
  collectHypotheses l.declName mvars bis mode
  return (newE, step)

/-- Convert an `IdLemma` into the `PullLemma` that `applyPullLemma` expects; an identity lemma is
just a pull lemma whose algebraic side is the element and which therefore has no holes. -/
def IdLemma.toPullLemma (l : IdLemma) : PullLemma where
  declName := l.declName
  prio := 1000
  ring := l.ring
  unital := l.unital
  cfcOnLhs := l.cfcOnLhs
  numHoles := 0

/-! ### Ordering candidate lemmas -/

/-- How far a `Pull` lemma is from applying at the mode we want: the key `pullCandidates` sorts
its candidates on, best (least) first.

The fields are compared lexicographically rather than combined into a number, because they are
not commensurable: one scalar conversion is not "as much cost" as one change of unitality, and
neither is a quantity of the same kind as an attribute priority. -/
structure Cost where
  /-- The number of `Scalar` lemmas that have to be composed to get from the lemma's scalar ring
  to the requested one; `0` when the lemma is usable at the requested ring outright. -/
  conversions : Nat
  /-- Whether a change of unitality is needed on top of that. -/
  changesUnitality : Bool
  /-- The lemma's `@[cfc_pull]` priority. Higher priority is *better*, so unlike the other
  fields this one is compared in reverse. -/
  prio : Nat
  /-- The number of holes on the lemma's algebraic side. Each hole is a recursive call, and
  each recursive call can leave side goals behind, so fewer is better: `cfc_pow_id`, whose
  algebraic side is `a ^ n`, beats `cfc_pow`, whose algebraic side is `cfc f a ^ n`. -/
  holes : Nat
  deriving Inhabited, Repr

instance : Ord Cost where
  compare a b :=
    compare a.conversions b.conversions
      |>.then (compare a.changesUnitality b.changesUnitality)
      |>.then (compare b.prio a.prio)
      |>.then (compare a.holes b.holes)

/-! ### The recursion -/

mutual

/-- Pull `e` towards `cfc f a` at the mode `want`. See `Spec.md` §6.2. -/
partial def pull (e : Expr) (want : Mode) : PullM Result := withIncDepth do
  -- `withTraceNode` prefixes its own success/failure emoji, so the message needs none
  withTraceNode `Tactic.cfc_pull (fun _ => return m!"pull {e} into a {want}") do
    let ctx ← read
    -- 1. the element itself
    if ← withReducible <| isDefEq e ctx.elem then
      for l in ctx.lemmas.id do
        let r ← observing? do
          convert (← applyPullLemma l.toPullLemma e want pull) want
        if let some r := r then return r
    -- 2. an application of the calculus
    if let some c := CFCApp.match? e then
      let r ← observing? do convert (← pullExisting c want) want
      if let some r := r then return r
    -- 3. tagged pull lemmas
    let candidates ← pullCandidates e want
    -- the expression is already in the enclosing trace node's message
    trace[Tactic.cfc_pull] "candidates: {candidates.map (ppConst ·.declName)}"
    for l in candidates do
      let r ← observing? do convert (← applyPullLemma l e want pull) want
      if let some r := r then return r
    -- 3b. tagged pull lemmas applied at some *other* element, followed by a composition
    for l in candidates do
      if l.numHoles != 0 then continue
      let r ← observing? do
        let (newE, step) ← applyLooseLemma l e want
        let res ← pull newE want
        return { res with proof := ← mkEqTrans step res.proof }
      if let some r := r then return r
    let head := match e.getAppFn.constName? with
      | some n => ppConst n
      | none => m!"_"
    let mut msg := m!"`cfc_pull` got stuck on `{e}`{indentD m!"(head symbol: \
      {head}, target: {want} at `{ctx.elem}`)"}"
    /- A local definition is an atom unless `+zetaDelta` is given, so a pull that reaches one
    stops dead with nothing to say about it: the head symbol printed above is `_`, as it is for
    any free variable, which on its own tells the user nothing. Name the flag instead. -/
    if !ctx.cfg.zetaDelta then
      if let .fvar fvarId := e.getAppFn then
        if (← fvarId.getDecl).isLet then
          msg := msg ++ m!"\n`{e.getAppFn}` is a local definition, and `cfc_pull` does not look\n\
            at what it stands for. Unfold it with `cfc_pull +zetaDelta ..`, or rewrite it away\n\
            first — `set .. with h` hands you the equation `h` to do it with."
    /- The one failure worth spelling out: `e` is already an application of the calculus, just
    to the wrong element. `cfc_pull` only ever rewrites the calculus at a *more* complicated
    element into the calculus at a simpler one, so this is a dead end, and it usually means the
    wrong element was named. -/
    if let some c := CFCApp.match? e then
      unless ← withNewMCtxDepth <| withReducible <| isDefEq c.elem ctx.elem do
        msg := msg ++ m!"\nThe calculus is already applied here, but to a different\n\
          element; `cfc_pull` only ever makes the element simpler, never more\n\
          complicated. If it is that element you meant to pull towards, name\n\
          it:{indentD m!"cfc_pull {want.ring} {c.elem}"}"
    throwError msg

/-- Handle `e = cfc g b`: either `b` is the element we are pulling towards, or we are looking at
a composition. -/
partial def pullExisting (c : CFCApp) (want : Mode) : PullM Result := do
  let ctx ← read
  let e := c.toExpr
  let mode := c.toMode
  if ← withReducible <| isDefEq c.elem ctx.elem then
    return { app := c, proof := ← mkEqRefl e }
  -- The calculus is applied to something else, so this is a composition.  Fix the unitality
  -- first: composing inside the non-unital calculus when the unital one was asked for would put
  -- a spurious `f 0 = 0` side goal on every piece of the inner expression.
  if c.unital != want.unital then
    for l in ctx.lemmas.unital do
      unless ← l.ring.matchesRing c.ring do continue
      let srcOnLhs := if want.unital then l.nonUnitalOnLhs else !l.nonUnitalOnLhs
      let r ← observing? do
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
    let r ← observing? do
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

/-- The `Pull` lemmas that could apply to `e`, best first, ordered by `Cost`: lemmas usable at
the requested scalar ring first and then by the length of the conversion chain, within that
those already at the requested unitality, then by attribute priority, then by number of holes.

Lemmas whose scalar ring the conversion graph cannot reach from the requested one are dropped
rather than ranked last; there is no point offering a candidate that is certain to fail. -/
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

end

/-! ### Entry point -/

/-- Determine the mode to work in: the scalar ring `R` as requested, and the unital calculus if
the configuration asks for it and the algebra supports it. Also returns the predicate. -/
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
it, and the side goals that proof depends on.

`lemmas` is the set to pull with. It is passed in rather than read from the environment here
because the bracketed lemma list of `cfc_pull` modifies it for the duration of one call. -/
def runPull (cfg : Config) (lemmas : Lemmas) (R elem e : Expr) :
    MetaM (Expr × Expr × Array (MVarId × SideGoalKind)) := do
  -- see the note in `cfcPullTarget`: nothing downstream looks through `mdata`
  let e := e.consumeMData
  let alg ← inferType elem
  unless ← isDefEq (← inferType e) alg do
    throwError "`cfc_pull`: `{e}` does not live in the algebra `{alg}`"
  let target ← mkMode cfg R alg
  let ctx : Context := { cfg, elem, alg, target, lemmas }
  -- Compute the predicate up front, so that "there is no such functional calculus" is reported
  -- as itself rather than as a pile of failed lemma applications.
  /- `zetaDelta` governs whether `isDefEq` and `whnf` — and so also the `DiscrTree` lookup that
  chooses the candidate lemmas — unfold a `let`-bound local to its value. It is `true` ambiently,
  which would make a local definition transparent to the whole pull; the default here is `false`,
  so that such a variable is an atom unless `+zetaDelta` asks otherwise. It is set around the
  recursion only, leaving the typing and instance questions above at the ambient configuration,
  for the same reason those are exempt from the reducible transparency (see the module
  docstring). -/
  let (res, st) ←
    try
      withConfig (fun c => { c with zetaDelta := cfg.zetaDelta }) <|
        ((do let _ ← getPredicate target; pull e target).run ctx).run {}
    catch ex =>
      if let .internal id _ := ex then
        if id == maxDepthExceptionId then
          throwError "`cfc_pull` reached its maximum recursion depth of {cfg.maxDepth}; either\n\
            the expression is more deeply nested than that, or the `@[cfc_pull]` lemma set is\n\
            looping. Raise the limit with `cfc_pull (maxDepth := {2 * cfg.maxDepth}) ..`"
      throw ex
  let goals ← st.sideGoals.filterM fun (g, _) => return !(← g.isAssigned)
  return (← instantiateMVars res.app.toExpr, ← instantiateMVars res.proof, goals)

end Mathlib.Tactic.CFCPull
