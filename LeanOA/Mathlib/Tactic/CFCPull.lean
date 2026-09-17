module

public import LeanOA.Mathlib.Tactic.CFCPull.Attr
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Parser.Tactic
public meta import Lean.Elab.Tactic.Conv.Basic
public meta import Lean.Elab.Tactic.Conv.Simp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public meta import LeanOA.Mathlib.Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.TryThis

/-!
# The `cfc_pull` tactic

`cfc_pull R a` rewrites the goal so that the continuous functional calculus over `R` is at the head
of every maximal subexpression whose type is that of `a`: each such subexpression becomes `cfc f a`
(or `cfcₙ f a`) for a function `f : R → R` read off its structure with the `@[cfc_pull]` lemmas.

It is `simp only` with those lemmas, plus what cannot be expressed without knowing `R` and `a`:

* *targets*: `a`, and the elements that the holes of a lemma with a structured element
  (`φ (cfc f a) = cfc f (φ a)`) are at when that element is a target, such as `x` in `φ x`;
* the `target` lemmas (`a = cfc id a`, `1 = cfc 1 a`, `star b = cfc star b`, ..), whose algebraic
  side does not determine the ring, instantiated at `R` (and, when the left-hand side is the bare
  element, at the target);
* priorities, boosted for lemmas at the ring `R` and the requested unitality;
* one pre-simproc on `cfc f b` / `cfcₙ f b`, which applies composition lemmas, simplifies `b`
  (never `f`) unless `b` is a target, and converts the scalar ring and unitality towards the
  requested ones (conversion lemmas are included only in that direction, so they cannot loop);
* one post-simproc, which flips the unitality of an argument when no lemma applies otherwise.

The lemmas are the real ones, hypotheses included. `simp` rejects a rewrite whose proof contains
an assignable metavariable, so the discharger cannot leave a goal behind; instead it fills each
hypothesis it cannot prove with a marked placeholder, which the tactic turns into a side goal once
`simp` is done (`deferDischarge`, `replacePlaceholders`). The side goals are then attempted with
a tactic chosen by their kind, and the survivors handed to the `=> ..` block.

## Unsupported

* **Compositions that also change the scalar ring.**
  `cfc_comp_re : cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A)` is a composition that changes the
  scalar ring from `ℝ` to `ℂ` on the way. The attribute classifies such a lemma as a composition
  at the ring of its simpler side, which is not enough: the composition would have to be followed
  by a conversion, at the inner element. These lemmas are deliberately left untagged.
* **Elements with a parameter.** `cfc_map_pi : cfc f a = fun i ↦ cfc f (a i)` has its hole at
  `a i` under a binder, so the element to pull towards is a family. Supporting it would take
  targets with parameters: `findTargets` keeping the binders a hole is under instead of skipping
  it, `isTargetElem` matching with fresh metavariables for them, and the `target` lemmas
  instantiated at the family, `∀ i, a i = cfc id (a i)`. Pairs (`cfc_map_prod`) need none of
  this: their holes are at the closed components.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta Elab Tactic Parser.Tactic

/-- Configuration for `cfc_pull`. -/
structure Config where
  /-- Prefer the unital calculus. -/
  unital : Bool := true
  /-- Hand every side goal to the `=> ..` block, attempting none. -/
  defer : Bool := false

declare_config_elab elabConfig Config

/-- What the `[..]` list of `cfc_pull` amounts to. -/
structure Lemmas where
  /-- The `cfc_pull` lemmas: the `@[cfc_pull]` set, adjusted by the list. -/
  entries : Array Entry
  /-- The simp context `simp` elaborated the rest of the list into: its lemmas, declarations and
  `let`-variables to unfold, and simp sets. -/
  ctx : Simp.Context
  /-- The simprocs of the list. -/
  simprocs : Simp.SimprocsArray := #[]

/-- An element pulled towards. -/
structure Target where
  /-- The element. -/
  elem : Expr
  /-- Its type. -/
  alg : Expr
  /-- Whether it has a unital calculus (and the user did not ask for a non-unital one). -/
  unital : Bool

/-- `ContinuousFunctionalCalculus R A p` with instance arguments synthesized. -/
def mkClassApp (clsName : Name) (args : Array Expr) : MetaM Expr := do
  let arity := (← getConstInfo clsName).type.getForallArity
  mkAppOptM clsName (args.map some ++ Array.replicate (arity - args.size) none)

/-- Whether `alg` has a (non-)unital calculus over `R`. -/
def hasCFC (unital : Bool) (R alg : Expr) : MetaM Bool := do
  let cls :=
    if unital then ``ContinuousFunctionalCalculus else ``NonUnitalContinuousFunctionalCalculus
  try
    let p ← mkFreshExprMVar (← mkArrow alg (.sort .zero))
    return (← synthInstance? (← mkClassApp cls #[R, alg, p])).isSome
  catch _ => return false

/-- The target at `s`, if its type has a calculus over `R`. -/
def mkTarget? (cfg : Config) (R s : Expr) : MetaM (Option Target) := do
  let alg ← instantiateMVars (← inferType s)
  if cfg.unital && (← hasCFC true R alg) then return some { elem := s, alg, unital := true }
  if ← hasCFC false R alg then return some { elem := s, alg, unital := false }
  return none

/-- The targets: `t` itself, and the elements that the holes of a lemma with a
structured element (`φ (cfc f a) = cfc f (φ a)`) are at when that element is a target. -/
partial def findTargets (cfg : Config) (entries : Array Entry) (R t : Expr) :
    MetaM (Array Target) := do
  let some tg ← mkTarget? cfg R t | return #[]
  go #[tg] #[t]
where
  go (out : Array Target) (todo : Array Expr) : MetaM (Array Target) := do
    let some t := todo.back? | return out
    let mut out := out
    let mut todo := todo.pop
    for e in entries do
      unless e.kind matches .pull | .target do continue
      unless e.holes do continue
      let found ← withoutModifyingState do
        let (_, _, ty) ← forallMetaTelescopeReducing (← inferType (← e.proof))
        let some (_, lhs, rhs) := ty.eq? | return #[]
        -- the calculus is on the right as `simp` sees the lemma
        let (lhs, rhs) := if e.inv then (rhs, lhs) else (lhs, rhs)
        let some (_, _, _, elem) := matchCFC? rhs | return #[]
        if elem.isMVar then return #[]
        unless ← withReducible <| isDefEq elem t do return #[]
        let holes ← IO.mkRef #[]
        (← instantiateMVars lhs).forEach fun h ↦ do
          if let some (_, _, _, b) := matchCFC? h then
            unless b.hasMVar || b.hasLooseBVars do holes.modify (·.push b)
        holes.get
      for b in found do
        if ← out.anyM fun o ↦ return o.elem == b then continue
        if let some tg ← mkTarget? cfg R b then
          out := out.push tg; todo := todo.push b
    go out todo

/-- What decides which of two lemmas is tried first, most significant first. -/
structure Rank where
  /-- The scalar conversions from the lemma's ring to the requested one; fewer first. A lemma
  generic in its ring needs none, and a ring not connected to the requested one is furthest. -/
  conversions : Nat
  /-- Whether the lemma is not at the requested unitality; the requested one first. -/
  flipped : Bool
  /-- The priority of the lemma; higher first. -/
  prio : Nat
  /-- For a `target` lemma, the index of the target it is instantiated at; earlier first. -/
  target : Nat

/-- `.gt` if `a` is tried before `b`. -/
def Rank.compare (a b : Rank) : Ordering :=
  (Ord.compare b.conversions a.conversions).then <| (Ord.compare b.flipped a.flipped).then <|
    (Ord.compare a.prio b.prio).then (Ord.compare b.target a.target)

/-- The `simp` priority realizing a rank among `ranks`: the number of them it is tried before. -/
def Rank.toPrio (ranks : Array Rank) (r : Rank) : Nat :=
  ranks.countP (r.compare · == .gt)

/-- Distances from the key of `R` in the graph of scalar conversions. -/
def ringDistances (R : Expr) (entries : Array Entry) : Array (Name × Nat) := Id.run do
  let some r := R.getAppFn.constName? | return #[]
  let edges := entries.filterMap fun e =>
    if e.kind == .conv && e.ring != e.srcRing then
      match e.ring, e.srcRing with
      | some a, some b => some (a, b)
      | _, _ => none
    else none
  let mut dist := #[(r, 0)]
  let mut frontier := #[r]
  for d in [1:edges.size + 1] do
    let mut next := #[]
    for n in frontier do
      for (a, b) in edges do
        for (x, y) in [(a, b), (b, a)] do
          if x == n && !dist.any (·.1 == y) then
            dist := dist.push (y, d); next := next.push y
    frontier := next
  return dist

/-- Instantiate a `target` lemma at `R` and a target: its ring is `R`, and its element is the
target itself if the left-hand side is the bare element, or else any element of the target's
algebra. The arguments this leaves undetermined are metavariables, for the caller to abstract;
`simp` synthesizes the instances among them at rewrite time. -/
def instantiateTarget (R : Expr) (t : Target) (e : Entry) (S : Expr := R) :
    MetaM (Option (Expr × Bool)) := do
  let c ← e.proof
  let (mvars, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, lhs, rhs) := ty.eq? | return none
  let (lhs, rhs) := if e.inv then (rhs, lhs) else (lhs, rhs)
  let some (R', _, _, elem) := matchCFC? rhs | return none
  unless ← isDefEq R' R do return none

  unless ← isDefEq (← inferType elem) t.alg do return none
  -- an element the left-hand side does not determine must be the target
  if elem.isMVar then
    unless ← isDefEq elem t.elem do return none
  -- a type nothing determines (the `S` of an `AlgHomClass F S A B`, which is not an `outParam`)
  -- is taken to be `S`; the caller tries `R` and the rings of the conversion graph
  let lhsTy ← instantiateMVars (← inferType lhs)
  for m in mvars do
    let m ← instantiateMVars m
    if m.isMVar && (← isType m) && (lhs.findMVar? (· == m.mvarId!)).isNone &&
        (lhsTy.findMVar? (· == m.mvarId!)).isNone then
      discard <| isDefEq m S
  -- an instance that can be found now is, and one that cannot rules the lemma out
  for (m, bi) in mvars.zip bis do
    if bi.isInstImplicit && (← instantiateMVars m).isMVar then
      let ty ← instantiateMVars (← inferType m)
      unless ty.hasExprMVar do
        let some inst ← synthInstance? ty | return none
        unless ← isDefEq m inst do return none
  let prf := c.beta mvars
  let prf ← if e.inv then mkEqSymm prf else pure prf
  return some (← instantiateMVars prf, lhs.isMVar)

/-- Add a `pull` lemma to a simp set, specialized to the ring `R` if it is generic in its ring.
Left generic, `cfc_const_mul_id : r * a = cfc (fun x ↦ r * x) a` would match `t • a` with `t : ℝ`
at a complex calculus, and the result be converted afterwards. -/
def addAt (R : Expr) (s : SimpTheorems) (e : Entry) (prio : Nat) : MetaM SimpTheorems := do
  if e.ring.isSome then return ← e.addTo s prio
  let c ← e.proof
  let (mvars, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, lhs, rhs) := ty.eq? | e.addTo s prio
  let some (R', _, _, _) := matchCFC? (if e.inv then lhs else rhs) | e.addTo s prio
  unless ← isDefEq R' R do return s
  let prf := c.beta mvars
  let prf ← if e.inv then mkEqSymm prf else pure prf
  let r ← abstractMVars (← instantiateMVars prf)
  s.add e.origin r.paramNames r.expr (prio := prio)

/-- Everything `simp` needs to pull towards one ring. -/
structure Setup where
  /-- The simp context. -/
  ctx : Simp.Context
  /-- The simprocs. -/
  simprocs : Simp.SimprocsArray
  /-- The discharger. -/
  disch : Simp.Discharge

/-- Whether `e` is (reducibly) one of the targets. -/
def isTargetElem (targets : Array Target) (e : Expr) : MetaM Bool :=
  let e := e.consumeMData
  targets.anyM fun t => do
    if e == t.elem then return true
    unless e.getAppFn == t.elem.getAppFn && e.getAppNumArgs == t.elem.getAppNumArgs do
      return false
    withNewMCtxDepth <| withReducible <| isDefEq e t.elem

/-- The congruence `e = e'`, where `e'` is `e` with the arguments at the positions in `rs`
replaced by the results there. -/
def congrArgs (e : Expr) (rs : Array (Nat × Simp.Result)) : MetaM Simp.Result := do
  let mut acc : Simp.Result := { expr := e.getAppFn }
  for (arg, i) in e.getAppArgs.zipIdx do
    acc ← match rs.find? (·.1 == i) with
      | some (_, r) => Simp.mkCongr acc r
      | none => Simp.mkCongrFun acc arg
  return acc

mutual

/-- The simp context and simprocs pulling towards `R`, cached per ring. -/
partial def getSetup (cfg : Config) (t : Expr) (lems : Lemmas) (disch : Simp.Discharge)
    (cache : IO.Ref (Array (Expr × Setup))) (stack : IO.Ref (Array Expr)) (R : Expr) :
    MetaM Setup := do
  let entries := lems.entries
  for (R', s) in ← cache.get do
    if ← withNewMCtxDepth <| isDefEq R R' then return s
  let targets ← findTargets cfg entries R t
  let dist := ringDistances R entries
  let distOf (n : Option Name) : Option Nat := n.bind fun n ↦ (dist.find? (·.1 == n)).map (·.2)
  -- a concrete ring that is not a node of the conversion graph is only usable if it is `R`
  let distOf (n : Option Name) : Option Nat :=
    if n == R.getAppFn.constName? then some 0 else distOf n
  let rank (e : Entry) (target : Nat := 0) : Rank :=
    { conversions := if e.ring.isNone then 0 else (distOf e.ring).getD (dist.size + 1)
      flipped := e.unital != cfg.unital, prio := e.prio, target }
  let ranks := entries.flatMap fun e ↦
    if e.kind == .target then (Array.range targets.size).map (rank e ·) else #[rank e]
  let prio (e : Entry) (target : Nat := 0) : Nat := (rank e target).toPrio ranks
  let mut pull : SimpTheorems := {}
  let mut loose : SimpTheorems := {}
  let mut conv : SimpTheorems := {}
  let mut flip : SimpTheorems := {}
  let mut compose : SimpTheorems := {}
  let mut tgt : SimpTheorems := {}
  let mut atom : SimpTheorems := {}
  for n in [``eq_self, ``iff_self, ``implies_true] do
    pull ← pull.addConst n
  for e in entries do
    match e.kind with
    | .pull =>
      if e.holes then pull ← addAt R pull e (prio e)
      else loose ← addAt R loose e (prio e)
    -- compositions and conversions apply at the ring of the calculus they meet, whatever it is
    | .compose => compose ← e.addTo compose (prio := prio e)
    | .conv =>
      if e.unital != e.srcUnital then
        flip ← e.addTo flip (prio := eval_prio default)
        -- towards the requested unitality
        if e.unital == cfg.unital then conv ← e.addTo conv (prio := 2000)
      else if let (some d, some d') := (distOf e.ring, distOf e.srcRing) then
        -- towards the requested ring
        if d < d' then conv ← e.addTo conv (prio := eval_prio default)
    | .target =>
      for (tg, i) in targets.zipIdx do
        let mut seen : Array Expr := #[]
        -- the rings of the conversion graph, all of which are constants
        for S in #[R] ++ dist.map (mkConst ·.1) do
          let some (prf, bare) ← instantiateTarget R tg e S | continue
          let r ← abstractMVars prf
          if seen.contains r.expr then continue
          seen := seen.push r.expr
          trace[Tactic.cfc_pull] "{← ppOrigin e.origin} at {tg.elem}: {← inferType prf}"
          let id := .other (e.origin.key ++ `inst)
          if bare then
            -- the unital and non-unital identity lemmas would otherwise compete on equal terms
            unless e.unital == tg.unital do continue
            atom ← atom.add id r.paramNames r.expr
          else if e.holes then
            tgt ← tgt.add id r.paramNames r.expr (prio := prio e i)
          else
            loose ← loose.add id r.paramNames r.expr (prio := prio e i)
  -- the rest of the list first: it is what the user asked for
  let ctx := lems.ctx.setSimpTheorems (lems.ctx.simpTheorems ++ #[pull, tgt])
  let procs := getSetup cfg t lems disch cache stack
  let simprocs : Simp.Simprocs := {
    pre := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcPullPre, post := false, keys := #[.star],
        proc := .inl (cfcPre R targets atom loose conv compose stack procs) }
    post := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcPullFlip, post := true, keys := #[.star],
        proc := .inl (flipPost flip #[pull, tgt]) } }
  let s := { ctx, simprocs := #[simprocs] ++ lems.simprocs, disch }
  cache.modify (·.push (R, s))
  return s

/-- The pre-simproc. A target is wrapped as `cfc id a` before `simp` can look inside it. On
`cfc f b`: compose; simplify `b` (never `f`) unless it is a target, at the ring of this `cfc` if
that is not the requested one, so that an inner element is pulled at the ring of the calculus
applied to it; and only then convert towards the requested unitality, then ring. When `b` is
itself the calculus applied to something other than a target, it is simplified *before* composing:
composing first would ask for the predicate at that something, when the target's is known. -/
partial def cfcPre (R : Expr) (targets : Array Target) (atom loose conv compose : SimpTheorems)
    (stack : IO.Ref (Array Expr)) (setup : Expr → MetaM Setup) : Simp.Simproc := fun e => do
  -- a target first of all: it may be an application of the calculus itself, and it is atomic:
  -- no lemma reads it as an expression in something else (`cfc_const` would read the target
  -- `algebraMap ℂ A z` as a constant)
  if ← isTargetElem targets e then
    if let some r ← Simp.rewrite? e atom.post atom.erased "cfc_pull atom" false then
      return .visit r
    return .continue
  let some (S, _, _, b) := matchCFC? e |
    if let some r ← Simp.rewrite? e loose.post loose.erased "cfc_pull loose" false then
      return .visit r
    return .continue
  unless e.getAppNumArgs == (← getConstInfo e.getAppFn.constName!).type.getForallArity do
    return .continue
  let isTarget ← isTargetElem targets b
  let innerElsewhere ← match matchCFC? b with
    | some (_, _, _, c) => pure (!isTarget && !(← isTargetElem targets c))
    | none => pure false
  let compose? : SimpM (Option Simp.Result) :=
    Simp.rewrite? e compose.post compose.erased "cfc_pull compose" false
  unless isTarget || innerElsewhere do
    if let some r ← compose? then return .visit r
  -- an element already being simplified further up is left alone, or `ψ a ↦ cfc id (ψ a)` loops
  if !isTarget && !(← stack.get).contains b then
    stack.modify (·.push b)
    let (rb, nestedUsed) ← try
        if ← withNewMCtxDepth <| isDefEq S R then pure (← Simp.simp b, #[]) else do
          let s ← setup S
          let (rb, stats) ← Simp.main b s.ctx
            (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
          pure (rb, stats.usedTheorems.toArray)
      finally stack.modify (·.pop)
    -- inside the calculus, only `b` becoming the calculus applied to something is progress
    -- (composition can then happen); `cfc f (a + b)` with `b` foreign is left alone rather than
    -- becoming `cfc f (cfc id a + b)`, and `cfc id b` itself would compose back to `e` and loop
    let progress := rb.expr != b && match matchCFC? rb.expr with
      | some (_, _, _, b') => b' != b
      | none => false
    if progress then
      -- the nested run has its own statistics; `cfc_pull?` wants its lemmas too
      for o in nestedUsed do Simp.recordSimpTheorem o
      return .visit (← Simp.mkCongrArg e.appFn! rb)
  if innerElsewhere then
    if let some r ← compose? then return .visit r
  if let some r ← Simp.rewrite? e conv.post conv.erased "cfc_pull conv" false then
    return .visit r
  return .done { expr := e }

/-- The post-simproc, run when no lemma applies to `e`: flip the unitality of the arguments that
are applications of the calculus — all of them together first, then each on its own — and try the
lemmas again. -/
partial def flipPost (flip : SimpTheorems) (thms : Array SimpTheorems) : Simp.Simproc := fun e => do
  if (matchCFC? e).isSome then return .continue
  let args := e.getAppArgs
  -- a flip that leads nowhere is not a use of the lemma, as far as `cfc_pull?` is concerned
  let used := (← get).usedTheorems
  let mut flips : Array (Nat × Simp.Result) := #[]
  for h : i in [0:args.size] do
    let arg := args[i]
    unless (matchCFC? arg).isSome do continue
    if let some r ← Simp.rewrite? arg flip.post flip.erased "cfc_pull flip" false then
      flips := flips.push (i, r)
  if flips.isEmpty then return .continue
  let candidates := if flips.size > 1 then #[flips] ++ flips.map (#[·]) else #[flips]
  for c in candidates do
    -- the congruence fails for a dependent function, `⟨cfc f a, h⟩ : {x // ..}` say
    let some r₁ ← (try some <$> congrArgs e c catch _ => pure none) | continue
    for s in thms do
      if let some r₂ ← Simp.rewrite? r₁.expr s.post s.erased "cfc_pull" false then
        return .visit (← r₁.mkEqTrans r₂)
  modify fun s => { s with usedTheorems := used }
  return .continue

end

/--
`cfc_pull R a` rewrites the goal so that the continuous functional calculus is at the head of
maximal subexpressions whose type matches that of `a`: each such subexpression is replaced by
`cfc f a` (or `cfcₙ f a`) for some function `f : R → R` that the tactic determines from the
structure of the expression and the collection of lemmas tagged `@[cfc_pull]`.

In the following example, `cfc_pull` acts on both sides of the equality, doing nothing with the
right-hand side, but expressing the left-hand side as `cfc (?f : R → R) a` where
`?f := fun x : R ↦ star x * x`, and the goal is closed with `rfl` at reducible transparency.

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a
```

* `cfc_pull R a`: with `a : A` attempts to write maximal subexpressions of the goal with type `A`
  in the form `cfc f a` for some function `f : R → R`, wherever they occur: under binders, and
  inside terms of other types. Side goals that cannot be discharged automatically are left open.
* `cfc_pull R a at h₁ h₂ ⊢`: rewrite the hypotheses `h₁` and `h₂` in the same way, and the goal
  (without `⊢`, the goal is left alone); `cfc_pull R a at *` rewrites everywhere it can.
* `cfc_pull -unital R a`: the same, but for `cfcₙ` instead; if only a non-unital instance of
  the continuous functional calculus can be found this is the default, whereas `cfc` is the default
  if a unital instance is found.
* `cfc_pull R a => tacticSeq`: discharge the side goals left unsolved with the supplied tactic
  script, which sees only those goals and must close all of them. `case cfc_pull.continuity => ..`
  and so on select goals by kind: `cfc_pull.predicate`, `cfc_pull.continuity`,
  `cfc_pull.mapZero` and `cfc_pull.side`.
* `cfc_pull +defer R a => tacticSeq`: attempt to discharge no side goals, and hand all of them to
  the `=> ..` block.
* `cfc_pull [lemma1, -lemma2, h, e] R a`: the list is that of `simp`. An equation with `cfc` or
  `cfcₙ` at the head of a side, such as `lemma1`, the local hypothesis `h`, or a term `hg n`, is
  added to the lemmas used by `cfc_pull`, as if it were tagged `@[cfc_pull]` (`cfc_pull` orients
  it, so `←`, `↓` and `↑` have no effect); `-lemma2` removes `lemma2`. Everything else is handed
  to `simp` as it is: rewrite rules, definitions and `let`-variables to unfold, simp sets,
  simprocs, `*`.
* `cfc_pull only [lemma1, lemma2] R a`: use only `lemma1` and `lemma2`, not the `@[cfc_pull]`
  lemmas.
* `cfc_pull? R a`: the same as `cfc_pull R a`, but suggests replacing itself with
  `cfc_pull only [..] R a`, listing the lemmas the rewrite used.

Side goals are first attempted with a tactic chosen by their kind: `cfc_cont_tac` for continuity,
`cfc_zero_tac` for `f 0 = 0`, and the predicate lemmas `cfc_predicate`/`cfcₙ_predicate` followed
by `cfc_tac` for the predicate of the calculus; `assumption` is tried on all of them.

Tracing of the `simp` call is available with `set_option trace.Meta.Tactic.simp true`, and of the
side goals with `set_option trace.Tactic.cfc_pull true`.
-/
syntax (name := cfcPull) "cfc_pull" optConfig (&" only")? (simpArgs)? ppSpace colGt term:max
  ppSpace colGt term:max (location)? (" => " colGt tacticSeq)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullTrace) "cfc_pull?" optConfig (&" only")? (simpArgs)? ppSpace colGt
  term:max ppSpace colGt term:max (location)? (" => " colGt tacticSeq)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull" optConfig (&" only")? (simpArgs)? ppSpace colGt
  term:max ppSpace colGt term:max (" => " colGt tacticSeq)? : conv

@[inherit_doc cfcPull]
syntax (name := cfcPullTraceConv) "cfc_pull?" optConfig (&" only")? (simpArgs)? ppSpace
  colGt term:max ppSpace colGt term:max (" => " colGt tacticSeq)? : conv

/-- Discharge a hypothesis with a local hypothesis if there is one, and otherwise with a
placeholder. `simp` rejects a rewrite whose proof contains an assignable metavariable, so the
placeholder is a `sorry`, marked so that `replacePlaceholders` can turn it into a goal
afterwards. -/
def deferDischarge (useHyps : Bool) : Simp.Discharge := fun e => do
  let e := (← instantiateMVars e).consumeTypeAnnotations
  if e.hasExprMVar then return none
  -- a class about types (`NonUnitalAlgHomClass F S A B`) is for instance synthesis, which has
  -- already failed; a class about an element (`IsStarNormal a`) is a side goal like any other
  if (← isClass? e).isSome then
    if ← e.getAppArgs.allM fun x ↦ isType x <||> return (← isClass? (← inferType x)).isSome then
      return none
  if useHyps then
    if let some h ← (← getLCtx).findDeclM? fun d ↦ do
        if !d.isImplementationDetail && (← withReducible <| isDefEq d.type e) then
          return some d.toExpr
        else return none then
      return some h
  return some <| .mdata (KVMap.empty.insert `cfcPullSideGoal (.ofBool true)) (← mkSorry e true)

/-- Replace the placeholders `deferDischarge` left in `proof` by new goals, one per statement.
`transform` enters the binders of the proof (the `funext` of a rewrite under `∀ n`, say) as local
hypotheses; a placeholder found under some is replaced by a goal quantified over them, applied
back to them. -/
def replacePlaceholders (proof : Expr) : MetaM (Expr × Array MVarId) := do
  let outer ← getLCtx
  let outerInsts ← getLocalInstances
  let goals ← IO.mkRef (#[] : Array (Expr × MVarId))
  let proof ← Meta.transform (← instantiateMVars proof) fun e => do
    let .mdata d b := e | return .continue
    unless d.contains `cfcPullSideGoal do return .continue
    let binders := (← getLCtx).foldl (init := #[]) fun xs d ↦
      if outer.contains d.fvarId || d.isImplementationDetail then xs else xs.push d.toExpr
    -- `b` is `sorryAx ty true`; a `let`-bound binder stays a `let` in the goal, so the goal is
    -- applied to the others only
    let ty ← mkForallFVars binders b.appFn!.appArg!
    let g ← match (← goals.get).find? (·.1 == ty) with
      | some (_, g) => pure g
      | none =>
        -- in the goal's context, not the binders': the goal quantifies over those
        let g ← withLCtx outer outerInsts <| mkFreshExprSyntheticOpaqueMVar ty
        goals.modify (·.push (ty, g.mvarId!))
        pure g.mvarId!
    let vars ← binders.filterM fun x ↦ return !(← x.fvarId!.getDecl).isLet
    return .done (mkAppN (.mvar g) vars)
  return (proof, (← goals.get).map (·.2))

/-- The lemma set for this call: the `@[cfc_pull]` set, or with `only` the empty set, adjusted by
the bracketed list. The list is elaborated by `simp`. The lemmas `cfc_pull` can classify are then
taken back out of the simp set: a tagged one keeps its entries, and so its priority; any other is
classified here, at `high` priority so that it outranks the tagged set. `-lemma` is `cfc_pull`'s
own: the simp set of the list starts empty, and `simp` would reject the erasure. -/
def elabLemmas (only : Bool) (args? : Option (TSyntax ``simpArgs)) : TacticM Lemmas := do
  let all := cfcPullExt.getState (← getEnv)
  let mut entries := if only then #[] else all
  let ctx ← Simp.mkContext (simpTheorems := #[{}])
  let some stx := args? | return { entries, ctx }
  let (erase, rest) := stx.raw[1].getSepArgs.partition (·.isOfKind ``simpErase)
  let list := mkNullNode #[mkAtom "[", mkNullNode (mkSepArray rest (mkAtom ",")), mkAtom "]"]
  let res ← elabSimpArgs list ctx #[] (eraseLocal := false) (kind := .simp)
  let mut thms := res.ctx.simpTheorems[0]!
  for (arg, r) in res.simpArgs do
    let #[thm] := r.simpTheorems | continue
    if entries.any (·.origin.key == thm.origin.key) then
      thms := thms.eraseCore thm.origin; continue
    let tagged := all.filter (·.origin.key == thm.origin.key)
    let new? ← if !tagged.isEmpty then pure (some tagged) else withRef arg do
      match thm.origin with
      | .decl n .. => mkEntries? (.decl n) (← getConstInfo n).type (eval_prio high)
      | o =>
        mkEntries? o (← inferType thm.proof) (eval_prio high) (some (thm.levelParams, thm.proof))
    let some new := new? | continue
    entries := entries ++ new
    thms := thms.eraseCore thm.origin
  if res.simpArgs.any (·.2 matches .star) then
    for h in ← getPropHyps do
      let some new ← mkEntries? (.fvar h) (← h.getType) (eval_prio high) | continue
      entries := entries ++ new
      thms := thms.eraseCore (.fvar h)
  let mut thmsArray := res.ctx.simpTheorems.set! 0 thms
  for arg in erase do
    let id := arg[1]
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    let o : Origin := .decl declName
    unless entries.any (·.origin.key == declName) || thmsArray.any (·.isLemma o) do
      throwErrorAt id "`{.ofConstName declName}` is not in the `cfc_pull` lemma set, so \
        `-{id}` has nothing to remove"
    entries := entries.filter (·.origin.key != declName)
    thmsArray := thmsArray.map (·.eraseCore o)
  return { entries, ctx := res.ctx.setSimpTheorems thmsArray, simprocs := res.simprocs }

/-- Elaborate the arguments of `cfc_pull`. -/
def elabArgs (cfgStx : TSyntax ``optConfig) (only : Bool)
    (lems? : Option (TSyntax ``simpArgs)) (ring elem : Term) :
    TacticM (Config × Setup × Array Entry) := do
  let cfg ← elabConfig cfgStx
  let R ← instantiateMVars (← Term.elabType ring)
  let t ← Term.elabTermAndSynthesize elem none
  let lems ← elabLemmas only lems?
  let s ← getSetup cfg t lems (deferDischarge !cfg.defer) (← IO.mkRef #[]) (← IO.mkRef #[]) R
  return (cfg, s, lems.entries)

/-- The lemma list `cfc_pull?` suggests. First the lemmas among `entries` that the run used, in
order of first use: declarations by the shortest names that resolve to them here, terms as they
were written. An instantiated `target` lemma is used under the origin `.other (key ++ `inst)`.
Then what `simp?` would list for the other lemmas used. -/
def mkOnlyLemmas (used : Simp.UsedSimps) (entries : Array Entry) :
    TacticM (TSyntax ``simpArgs) := do
  let mut args : Array Syntax := #[]
  let mut seen : Array Name := #[]
  let mut rest : Simp.UsedSimps := {}
  for o in used.toArray do
    let key := match o with
      | .other n => n.getPrefix
      | _ => o.key
    match entries.find? (·.origin.key == key) with
    | none =>
      -- the lemmas `getSetup` adds by itself
      unless [``eq_self, ``iff_self, ``implies_true].contains key do rest := rest.insert o
    | some e =>
      if seen.contains key then continue
      seen := seen.push key
      match e.origin with
      | .decl n .. =>
        let id := mkIdent (← unresolveNameGlobalAvoidingLocals n)
        args := args.push (← `(simpLemma| $id:ident))
      | .fvar id => args := args.push (← `(simpLemma| $(mkIdent (← id.getUserName)):ident))
      | .stx _ ref => args := args.push ref
      | .other _ => continue
  let simpOnly ← mkSimpOnly (← `(tactic| simp only [])) rest
  args := args ++ simpOnly[simpParamsPos][1].getSepArgs
  let list := mkNullNode (mkSepArray args (mkAtom ","))
  return ⟨mkNode ``simpArgs #[mkAtom "[", list, mkAtom "]"]⟩

/-- Run `tac` on `g`, returning `true` iff it closes the goal; otherwise restore the state. -/
def closes (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  -- runtime exceptions too: `cfc_zero_tac` can loop, on `0 = f 0` say
  let ok ← Term.withoutErrToSorry <| tryCatchRuntimeEx
    (return (← Tactic.run g tac).isEmpty) fun _ => pure false
  unless ok do saved.restore
  return ok

/-- The side goals, deduplicated, tagged by kind, and without those the tactic for their kind
closes: `cfc_cont_tac` for continuity, `cfc_zero_tac` for `f 0 = 0`, the predicate lemmas and
`cfc_tac` for the predicate of the calculus, and `assumption` for all. -/
def sideGoals (cfg : Config) (goals : Array MVarId) : TacticM (List MVarId) := do
  let mut out : Array MVarId := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if let some g' ← out.findM? fun g' => do withReducible <| isDefEq ty (← g'.getType) then
      g.assign (.mvar g'); continue
    -- a goal raised under a binder is quantified, so it is classified by its body
    let body := ty.getForallBody
    let isNonneg := body.le?.any fun (_, lhs, _) ↦ lhs.zero?
    let mentions (n : Name) := (body.find? (·.isConstOf n)).isSome
    let (tag, tacs) ←
      if body.isAppOf ``IsSelfAdjoint || body.isAppOf ``IsStarNormal || isNonneg then
        pure (`cfc_pull.predicate, #[← `(tactic| exact cfc_predicate _ _),
          ← `(tactic| exact cfcₙ_predicate _ _), ← `(tactic| cfc_tac)])
      else if mentions ``Continuous || mentions ``ContinuousOn then
        pure (`cfc_pull.continuity, #[← `(tactic| cfc_cont_tac)])
      else if body.eq?.any (·.2.2.zero?) then
        pure (`cfc_pull.mapZero, #[← `(tactic| cfc_zero_tac)])
      else
        pure (`cfc_pull.side, #[← `(tactic| exact cfc_predicate _ _),
          ← `(tactic| exact cfcₙ_predicate _ _)])
    g.setTag tag
    let tacs ← if cfg.defer then pure #[] else pure (#[← `(tactic| assumption)] ++ tacs)
    let closed ← tacs.anyM fun tac ↦ do closes g (evalTactic (← `(tactic| (intros; $tac))))
    trace[Tactic.cfc_pull] "side goal {ty}: {if closed then "closed" else "unsolved"}"
    unless closed do out := out.push g
  return out.toList

/-- Turn the placeholders in `proof` into side goals and deal with them: those the tactic for
their kind does not close are handed to the `=> ..` block, if there is one. -/
def dischargeSideGoals (cfg : Config) (proof : Expr) (arrow? : Option Syntax)
    (tac? : Option (TSyntax ``tacticSeq)) : TacticM Expr := do
  let (proof, goals) ← replacePlaceholders proof
  let side ← sideGoals cfg goals
  appendGoals side
  if let (some arrow, some tac) := (arrow?, tac?) then
    withRef arrow <| focusGoalsAndDone side.contains (evalTactic tac)
  return proof

@[tactic cfcPull, tactic cfcPullTrace]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let (tk, cfgStx, only?, lems?, ring, elem, loc?, arrow?, tac?) ← match stx with
    | `(tactic| cfc_pull%$tk $cfgStx:optConfig $[only%$only?]? $[$lems?]? $ring $elem
        $[$loc?:location]? $[=>%$arrow? $tac?]?)
    | `(tactic| cfc_pull?%$tk $cfgStx:optConfig $[only%$only?]? $[$lems?]? $ring $elem
        $[$loc?:location]? $[=>%$arrow? $tac?]?) =>
      pure (tk, cfgStx, only?, lems?, ring, elem, loc?, arrow?, tac?)
    | _ => throwUnsupportedSyntax
  withRef tk do
  let (cfg, s, entries) ← elabArgs cfgStx only?.isSome lems? ring elem
  let root ← getMainGoal
  let loc := expandOptLocation (mkOptionalNode loc?)
  let stats ← simpLocation s.ctx s.simprocs s.disch loc
  -- close the goal if it is now `rfl` up to reducible unfolding
  unless (← getGoals).isEmpty do
    if loc matches .wildcard || loc matches .targets _ true then
      evalTactic (← `(tactic| try with_reducible rfl))
  if stx.isOfKind ``cfcPullTrace then
    -- only the part up to the element is replaced, leaving any location and block as written
    let lems ← mkOnlyLemmas stats.usedTheorems entries
    let sugg ← `(tactic| cfc_pull%$tk $cfgStx:optConfig only $lems $ring $elem)
    TryThis.addSuggestion tk sugg (origSpan? := mkNullNode #[tk, elem])
  root.assign (← dischargeSideGoals cfg (.mvar root) arrow? tac?)

@[tactic cfcPullConv, tactic cfcPullTraceConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let (tk, cfgStx, only?, lems?, ring, elem, arrow?, tac?) ← match stx with
    | `(conv| cfc_pull%$tk $cfgStx:optConfig $[only%$only?]? $[$lems?]? $ring $elem
        $[=>%$arrow? $tac?]?)
    | `(conv| cfc_pull?%$tk $cfgStx:optConfig $[only%$only?]? $[$lems?]? $ring $elem
        $[=>%$arrow? $tac?]?) =>
      pure (tk, cfgStx, only?, lems?, ring, elem, arrow?, tac?)
    | _ => throwUnsupportedSyntax
  withRef tk do
  let (cfg, s, entries) ← elabArgs cfgStx only?.isSome lems? ring elem
  let lhs ← instantiateMVars (← Conv.getLhs)
  let (r, stats) ← Simp.main lhs s.ctx
    (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
  if r.expr == lhs then throwError "`cfc_pull` made no progress"
  if stx.isOfKind ``cfcPullTraceConv then
    let lems ← mkOnlyLemmas stats.usedTheorems entries
    let sugg ← `(conv| cfc_pull%$tk $cfgStx:optConfig only $lems $ring $elem)
    TryThis.addSuggestion tk sugg (origSpan? := mkNullNode #[tk, elem])
  let proof ← dischargeSideGoals cfg (← r.getProof) arrow? tac?
  Conv.applySimpResult { r with proof? := some proof }

end Mathlib.Tactic.CFCPull
