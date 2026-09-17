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
(or `cfcₙ f a`) for a function `f : R → R`. This is a wrapper around a simproc that uses lemmas
tagged with the `@[cfc_pull]` attribute.

It is `simp only` with those lemmas, plus what cannot be expressed without knowing `R` and `a`:

* *targets*: `a` (or each of the elements given, if several), and the elements that the holes of
  a lemma with a structured element (`φ (cfc f a) = cfc f (φ a)`) are at when that element is a
  target, such as `x` in `φ x`;
* the `target` lemmas (`a = cfc id a`, `1 = cfc 1 a`, `star b = cfc star b`, ..), whose algebraic
  side does not determine the ring, specialized at `R`. `simp` finds the element by unification,
  and the rewrite is accepted if that element is a target; only when the algebraic side is the
  bare element, or does not mention it, is the lemma instantiated at each target as well;
* the order of the simp sets. The lemmas `simp` can use on its own are put in simp sets when they
  are tagged, one for each use, ring and unitality; for each use, the sets at fewer scalar
  conversions from `R` are tried first, then those at the requested unitality;
* one pre-simproc on `cfc f b` / `cfcₙ f b`, which applies composition lemmas, simplifies `b`
  (never `f`) unless `b` is a target, and converts the scalar ring and unitality towards the
  requested ones (conversion lemmas are included only in that direction, so they cannot loop);
* one post-simproc, which flips the unitality of an argument when no lemma applies otherwise;
  and, when there are several elements of one type, pulls a constant argument towards the target
  the other arguments are at (`siblingPost`): the `target` lemmas for constants, which would send
  every `1` to the first target, are then left out.
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

/-- The decomposition of the `[..]` list of `cfc_pull` into `cfc` lemmas, and the simp context. -/
structure Lemmas where
  /-- The `cfc_pull` lemmas and their simp sets: the `@[cfc_pull]` ones, adjusted by the list. -/
  state : State
  /-- The simp context `simp` elaborated the rest of the list into. -/
  ctx : Simp.Context
  /-- The simprocs of the list. -/
  simprocs : Simp.SimprocsArray := #[]

/-- An element `cfc_pull` pulls towards. -/
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

/-- The targets: the `roots` themselves, and the elements that the holes of a lemma with a
structured element (`φ (cfc f a) = cfc f (φ a)`) are at when that element is a target. -/
partial def findTargets (cfg : Config) (entries : Array Entry) (R : Expr) (roots : Array Expr) :
    MetaM (Array Target) := do
  let tgs ← roots.filterMapM (mkTarget? cfg R)
  go tgs (tgs.map (·.elem)).reverse
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

/-- Specialize a `target` lemma at the ring `R` and, if it is given, at a target, which is then
the element of the lemma. The arguments this leaves undetermined are metavariables, for the caller
to abstract; `simp` synthesizes the instances among them at rewrite time. Also returned is whether
the left-hand side is the bare element. -/
def instantiateTarget (R : Expr) (t? : Option Target) (e : Entry) (S : Expr := R) :
    MetaM (Option (Expr × Bool)) := do
  let prf ← e.proof
  let (mvars, bis, ty) ← forallMetaTelescopeReducing (← inferType prf)
  let some (_, lhs, rhs) := ty.eq? | return none
  let (lhs, rhs) := if e.inv then (rhs, lhs) else (lhs, rhs)
  let some (R', _, _, elem) := matchCFC? rhs | return none
  unless ← isDefEq R' R do return none
  if let some t := t? then
    unless ← isDefEq (← inferType elem) t.alg do return none
    unless ← isDefEq elem t.elem do return none
  -- a type not appearing in the goal, the `S` of `StarAlgHomClass.map_cfc` say, is taken to
  -- be `S`; the caller tries `R` and the rings of the conversion graph.
  let lhsTy ← instantiateMVars (← inferType lhs)
  for m in mvars do
    let m ← instantiateMVars m
    if m.isMVar && (← isType m) && (lhs.findMVar? (· == m.mvarId!)).isNone &&
        (lhsTy.findMVar? (· == m.mvarId!)).isNone then
      discard <| isDefEq m S
  -- the instances are left to `simp`, which synthesizes them when it rewrites, and only for the
  -- lemmas it uses. With a guessed type they are what tells a good guess from a bad one: an
  -- instance that can be found now is, and one that cannot rules the guess out
  for (m, bi) in mvars.zip bis do
    if e.freeType && bi.isInstImplicit && (← instantiateMVars m).isMVar then
      let ty ← instantiateMVars (← inferType m)
      unless ty.hasExprMVar do
        let some inst ← synthInstance? ty | return none
        unless ← isDefEq m inst do return none
  let prf ← if e.inv then mkEqSymm (prf.beta mvars) else pure (prf.beta mvars)
  return some (← instantiateMVars prf, lhs.isMVar)

/-- Everything `simp` needs to pull towards one ring. -/
structure Setup where
  /-- The simp context. -/
  ctx : Simp.Context
  /-- The simprocs. -/
  simprocs : Simp.SimprocsArray
  /-- The discharger. -/
  disch : Simp.Discharge

/-- What one call of `cfc_pull` works with, from start to finish. The simprocs run in `SimpM`, at
`simp`'s pace and in nested runs of it, so what they share and change, the `cache`, is in a
reference. -/
structure Context where
  /-- The configuration. -/
  cfg : Config
  /-- The lemmas. -/
  lems : Lemmas
  /-- The discharger. -/
  disch : Simp.Discharge
  /-- The setups built so far, by ring and roots: the rings and roots needed are only found out
  during the run, and a setup is expensive. -/
  cache : IO.Ref (Array (Expr × Array Expr × Setup))

/-- `MetaM` with the `Context` of the call. -/
abbrev PullM := ReaderT Context MetaM

/-- Whether `e` is (reducibly) one of the targets. This must not miss: `cfcPre` simplifies an
element that is not a target, and if that produces the calculus applied to the same element (as
it does when the element is a target after all), it does so again, without end. -/
def isTargetElem (targets : Array Target) (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  let env ← getEnv
  -- an application of the constructor of a structure: `(c.1, c.2)` is the target `c`, by eta
  let isStructMk (e : Expr) : Bool := match e.getAppFn with
    | .const n _ => match env.find? n with
      | some (.ctorInfo i) => isStructure env i.induct
      | _ => false
    | _ => false
  targets.anyM fun t => do
    if e == t.elem then return true
    if isStructMk e != isStructMk t.elem then
      return ← withNewMCtxDepth <| withReducible <| isDefEq e t.elem
    -- a cheap filter; the heads are compared up to universe levels, which may be the same without
    -- being written the same (after a rewrite with a lemma at other level parameters, say)
    let sameHead := match e.getAppFn, t.elem.getAppFn with
      | .const n _, .const n' _ => n == n'
      | f, f' => f == f'
    unless sameHead && e.getAppNumArgs == t.elem.getAppNumArgs do return false
    withNewMCtxDepth <| withReducible <| isDefEq e t.elem

/-- Rewrite with the first of the simp sets that has a lemma for `e`. -/
def rewriteAny (sets : Array SimpTheorems) (e : Expr) (tag : String) :
    SimpM (Option Simp.Result) := do
  for s in sets do
    if let some r ← Simp.rewrite? e s.post s.erased tag false then return some r
  return none

/-- Rewrite with lemmas in which `simp` finds the element by unification: the rewrite is accepted
if it is towards a target, `star a ↦ cfc star a` but not `star b ↦ cfc star b`, and at the ring
`R?`, if that is given. -/
def rewriteTowards (targets : Array Target) (sets : Array SimpTheorems) (e : Expr)
    (R? : Option Expr := none) : SimpM (Option Simp.Result) := do
  -- a rewrite turned down is not a use of the lemma, as far as `cfc_pull?` is concerned
  let used := (← get).usedTheorems
  for s in sets do
    let some r ← Simp.rewrite? e s.post s.erased "cfc_pull towards" false | continue
    if let some (S, _, _, b) := matchCFC? r.expr then
      let ringOk ← match R? with
        | some R => withNewMCtxDepth <| isDefEq S R
        | none => pure true
      if ringOk && (← isTargetElem targets b) then return some r
    modify fun st ↦ { st with usedTheorems := used }
  return none

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

/-- The simp context and simprocs pulling towards the `roots` at `R`, cached per ring and
roots. -/
partial def getSetup (roots : Array Expr) (R : Expr) : PullM Setup := do
  let c ← read
  let { cfg, lems, disch, cache, .. } := c
  let entries := lems.state.entries
  for (R', roots', s) in ← cache.get do
    if roots == roots' && (← withNewMCtxDepth <| isDefEq R R') then return s
  let targets ← findTargets cfg entries R roots
  -- a constant belongs to no target in particular if another root shares the algebra
  let shared ← targets.mapM fun tg ↦ do
    let same ← roots.filterM fun r ↦ do
      withNewMCtxDepth <| isDefEq (← inferType r) tg.alg
    return decide (same.size > 1)
  let dist := ringDistances R entries
  let distOf (n : Option Name) : Option Nat := n.bind fun n ↦ (dist.find? (·.1 == n)).map (·.2)
  -- a concrete ring that is not a node of the conversion graph is only usable if it is `R`
  let distOf (n : Option Name) : Option Nat :=
    if n == R.getAppFn.constName? then some 0 else distOf n
  let mut st := lems.state
  let mut atom : SimpTheorems := {}
  -- the lemmas `simp` cannot use on its own; the others are in the simp sets of `st` already
  for e in entries do
    unless e.kind == .target do continue
    -- a lemma towards a structured element, `φ a`, is of use only if a target is of that shape;
    -- those with a free type are worth the check, being specialized at several rings each
    if e.freeType && e.elemHead.isSome &&
        !targets.any (·.elem.consumeMData.getAppFn.constName? == e.elemHead) then continue
    let id := .other (e.origin.key ++ `inst)
    let add (st : State) (set : SetKind) (r : AbstractMVarsResult) : MetaM State := do
      let thms ← mkSimpTheoremFromExpr id r.paramNames r.expr (prio := e.prio)
      return st.insert { set, ring := none, unital := e.unital } thms
    unless e.elemFree do
      -- `simp` finds the element, and the simprocs accept it if it is a target
      let mut seen : Array Expr := #[]
      -- a type the lemma leaves free is guessed among the rings of the conversion graph, all of
      -- which are constants
      for S in if e.freeType then #[R] ++ dist.map (mkConst ·.1) else #[R] do
        let some (prf, _) ← instantiateTarget R none e S | continue
        let r ← abstractMVars prf
        if seen.contains r.expr then continue
        seen := seen.push r.expr
        trace[Tactic.cfc_pull] "{← ppOrigin e.origin} at {R}: {← inferType prf}"
        st ← add st (if e.holes then .towards else .looseTowards) r
      continue
    for (tg, i) in targets.zipIdx do
      let some (prf, bare) ← instantiateTarget R tg e | continue
      let r ← abstractMVars prf
      trace[Tactic.cfc_pull] "{← ppOrigin e.origin} at {tg.elem}: {← inferType prf}"
      if bare then
        -- the unital and non-unital identity lemmas would otherwise compete on equal terms
        unless e.unital == tg.unital do continue
        atom ← atom.add id r.paramNames r.expr
      -- a constant (`1 = cfc 1 a`) is any target's, which is of no use when there are several
      else if shared[i]! then continue
      else st ← add st (if e.holes then .pull else .loose) r
  -- the simp sets for one use, in the order they are tried in: fewer scalar conversions first,
  -- then the requested unitality
  let weight (k : Key) : Nat :=
    2 * (if k.ring.isNone then 0 else (distOf k.ring).getD (dist.size + 1)) +
      (if k.unital == cfg.unital then 0 else 1)
  let sets := st.sets.qsort fun (k, _) (k', _) ↦
    weight k < weight k' || (weight k == weight k' && toString k.ring < toString k'.ring)
  let ordered (set : SetKind) : Array SimpTheorems := (sets.filter (·.1.set == set)).map (·.2)
  let pull := ordered .pull
  let towards := ordered .towards
  -- conversions between the two calculi, and those among them towards the requested unitality;
  -- then those towards the requested ring. They apply at the ring of the calculus they meet
  let convs := sets.filter (·.1.set == .conv)
  let flip := (convs.filter fun (k, _) ↦ k.unital != k.srcUnital).map (·.2)
  let conv := (convs.filter fun (k, _) ↦ k.unital != k.srcUnital && k.unital == cfg.unital) ++
    convs.filter fun (k, _) ↦ k.unital == k.srcUnital &&
      match distOf k.ring, distOf k.srcRing with
      | some d, some d' => d < d'
      | _, _ => false
  let conv := conv.map (·.2)
  let mut builtin : SimpTheorems := {}
  for n in [``eq_self, ``iff_self, ``implies_true] do
    builtin ← builtin.addConst n
  -- the rest of the list first: it is what the user asked for
  let ctx := lems.ctx.setSimpTheorems (lems.ctx.simpTheorems ++ #[builtin] ++ pull)
  let tgtPost : Simp.Simproc := fun e ↦ do
    let some r ← rewriteTowards targets towards e | return .continue
    return .visit r
  let post := tgtPost >> flipPost targets flip pull towards
  let post := if shared.any id then post >> siblingPost c R targets else post
  let simprocs : Simp.Simprocs := {
    pre := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcPullPre, post := false, keys := #[.star],
        proc := .inl (cfcPre c roots R targets atom (ordered .loose) (ordered .looseTowards) conv
          (ordered .compose)) }
    post := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcPullPost, post := true, keys := #[.star], proc := .inl post } }
  let s := { ctx, simprocs := #[simprocs] ++ lems.simprocs, disch }
  cache.modify (·.push (R, roots, s))
  return s

/-- The pre-simproc. A target is wrapped as `cfc id a` before `simp` can look inside it. On
`cfc f b`: compose; simplify `b` (never `f`) unless it is a target, at the ring of this `cfc` if
that is not the requested one, so that an inner element is pulled at the ring of the calculus
applied to it; and only then convert towards the requested unitality, then ring. When `b` is
itself the calculus applied to something other than a target, it is simplified *before* composing:
composing first would ask for the predicate at that something, when the target's is known. -/
partial def cfcPre (c : Context) (roots : Array Expr) (R : Expr) (targets : Array Target)
    (atom : SimpTheorems) (loose looseTowards conv compose : Array SimpTheorems) : Simp.Simproc :=
    fun e => do
  -- a target first of all: it may be an application of the calculus itself, and it is atomic:
  -- no lemma reads it as an expression in something else (`cfc_const` would read the target
  -- `algebraMap ℂ A z` as a constant)
  if ← isTargetElem targets e then
    if let some r ← Simp.rewrite? e atom.post atom.erased "cfc_pull atom" false then
      return .visit r
    return .continue
  let some (S, _, _, b) := matchCFC? e |
    if let some r ← rewriteAny loose e "cfc_pull loose" then return .visit r
    if let some r ← rewriteTowards targets looseTowards e R then return .visit r
    return .continue
  unless e.getAppNumArgs == (← getConstInfo e.getAppFn.constName!).type.getForallArity do
    return .continue
  let isTarget ← isTargetElem targets b
  let innerElsewhere ← match matchCFC? b with
    | some (_, _, _, c) => pure (!isTarget && !(← isTargetElem targets c))
    | none => pure false
  let compose? : SimpM (Option Simp.Result) :=
    rewriteAny compose e "cfc_pull compose"
  unless isTarget || innerElsewhere do
    if let some r ← compose? then return .visit r
  if !isTarget then
    let (rb, nestedUsed) ←
      if ← withNewMCtxDepth <| isDefEq S R then pure (← Simp.simp b, #[]) else do
        let s ← (getSetup roots S).run c
        let (rb, stats) ← Simp.main b s.ctx
          (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
        pure (rb, stats.usedTheorems.toArray)
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
  if let some r ← rewriteAny conv e "cfc_pull conv" then return .visit r
  return .done { expr := e }

/-- The post-simproc, run when no lemma applies to `e`: flip the unitality of the arguments that
are applications of the calculus — all of them together first, then each on its own — and try the
lemmas again. -/
partial def flipPost (targets : Array Target) (flip pull towards : Array SimpTheorems) :
    Simp.Simproc := fun e => do
  if (matchCFC? e).isSome then return .continue
  let args := e.getAppArgs
  -- a flip that leads nowhere is not a use of the lemma, as far as `cfc_pull?` is concerned
  let used := (← get).usedTheorems
  let mut flips : Array (Nat × Simp.Result) := #[]
  for h : i in [0:args.size] do
    let arg := args[i]
    unless (matchCFC? arg).isSome do continue
    if let some r ← rewriteAny flip arg "cfc_pull flip" then flips := flips.push (i, r)
  if flips.isEmpty then return .continue
  let candidates := if flips.size > 1 then #[flips] ++ flips.map (#[·]) else #[flips]
  for c in candidates do
    -- the congruence fails for a dependent function, `⟨cfc f a, h⟩ : {x // ..}` say
    let some r₁ ← (try some <$> congrArgs e c catch _ => pure none) | continue
    if let some r₂ ← rewriteAny pull r₁.expr "cfc_pull" then
      return .visit (← r₁.mkEqTrans r₂)
    if let some r₂ ← rewriteTowards targets towards r₁.expr then
      return .visit (← r₁.mkEqTrans r₂)
  modify fun s => { s with usedTheorems := used }
  return .continue

/-- The post-simproc for several targets in one algebra, where a constant (`1`, `algebraMap R A r`,
`1 + 1`) is not pulled on sight, there being no telling towards which target. Here it is an
argument next to applications of the calculus that are all at one target, and is pulled towards
that one alone. -/
partial def siblingPost (c : Context) (R : Expr) (targets : Array Target) : Simp.Simproc :=
    fun e => do
  if (matchCFC? e).isSome then return .continue
  let args := e.getAppArgs
  let mut elems : Array Expr := #[]
  for arg in args do
    if let some (_, _, _, b) := matchCFC? arg then
      if (← isTargetElem targets b) && !elems.contains b then elems := elems.push b
  let #[b] := elems | return .continue
  let alg ← inferType b
  let mut pulled : Array (Nat × Simp.Result) := #[]
  for h : i in [0:args.size] do
    let arg := args[i]
    if (matchCFC? arg).isSome then continue
    unless ← withReducible <| isDefEq (← inferType arg) alg do continue
    let s ← (getSetup #[b] R).run c
    let (r, stats) ← Simp.main arg s.ctx
      (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
    let some (_, _, _, b') := matchCFC? r.expr | continue
    unless b' == b do continue
    for o in stats.usedTheorems.toArray do Simp.recordSimpTheorem o
    pulled := pulled.push (i, r)
  if pulled.isEmpty then return .continue
  let some r ← (try some <$> congrArgs e pulled catch _ => pure none) | return .continue
  return .visit r

end

/-- The elements `cfc_pull` pulls towards. What follows them, `only` and `[..]`, would otherwise
be read as one more. -/
syntax cfcPullElems := (ppSpace colGt !&"only" !"[" term:max)+

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
* `cfc_pull R a b`: pull towards several elements at once, each subexpression towards the element
  it is an expression in. When two of the elements have the same type, a constant (`1`,
  `algebraMap R A r`) is pulled towards the element its neighbours are at, as the `1` of `b + 1`
  is, and left alone if it has none.
* `cfc_pull R a at h₁ h₂ ⊢`: rewrite the hypotheses `h₁` and `h₂` in the same way, and the goal
  (without `⊢`, the goal is left alone); `cfc_pull R a at *` rewrites everywhere it can.
* `cfc_pull -unital R a`: the same, but for `cfcₙ` instead; if only a non-unital instance of
  the continuous functional calculus can be found this is the default, whereas `cfc` is the default
  if a unital instance is found.
* `cfc_pull R a => tacticSeq`: discharge the side goals left unsolved with the supplied tactic
  script, which sees only those goals and must close all of them. `case cfc_pull.continuity => ..`
  and so on select goals by kind: `cfc_pull.predicate`, `cfc_pull.continuity`,
  `cfc_pull.mapZero` and `cfc_pull.side`.
* `cfc_pull (disch := tacticSeq) R a`: try `tacticSeq` on the `cfc_pull.side` goals, the side goals
  that are neither about continuity, nor `f 0 = 0`, nor the predicate of the calculus, and that
  `cfc_pull` has no tactic of its own for. Those it does not close are left, or handed to the
  `=> ..` block, as usual.
* `cfc_pull +defer R a => tacticSeq`: attempt to discharge no side goals, and hand all of them to
  the `=> ..` block.
* `cfc_pull R a [lemma1, -lemma2, h, e]`: the list is that of `simp`. An equation with `cfc` or
  `cfcₙ` at the head of a side, such as `lemma1`, the local hypothesis `h`, or a term `hg n`, is
  added to the lemmas used by `cfc_pull`, as if it were tagged `@[cfc_pull]` (`cfc_pull` orients
  it, so `←`, `↓` and `↑` have no effect); `-lemma2` removes `lemma2`. Everything else is handed
  to `simp` as it is: rewrite rules, definitions and `let`-variables to unfold, simp sets,
  simprocs, `*`.
* `cfc_pull R a only [lemma1, lemma2]`: use only `lemma1` and `lemma2`, not the `@[cfc_pull]`
  lemmas.
* `cfc_pull? R a`: the same as `cfc_pull R a`, but suggests replacing itself with
  `cfc_pull R a only [..]`, listing the lemmas the rewrite used.

Side goals are first attempted with a tactic chosen by their kind: `cfc_cont_tac` for continuity,
`cfc_zero_tac` for `f 0 = 0`, and the predicate lemmas `cfc_predicate`/`cfcₙ_predicate` followed
by `cfc_tac` for the predicate of the calculus; `assumption` is tried on all of them.

Tracing of the `simp` call is available with `set_option trace.Meta.Tactic.simp true`, and of the
side goals with `set_option trace.Tactic.cfc_pull true`.
-/
syntax (name := cfcPull) "cfc_pull" optConfig (discharger)? ppSpace colGt term:max
  cfcPullElems (&" only")? (simpArgs)? (location)? (" => " colGt tacticSeq)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullTrace) "cfc_pull?" optConfig (discharger)? ppSpace colGt
  term:max cfcPullElems (&" only")? (simpArgs)? (location)? (" => " colGt tacticSeq)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull" optConfig (discharger)? ppSpace colGt term:max
  cfcPullElems (&" only")? (simpArgs)? (" => " colGt tacticSeq)? : conv

@[inherit_doc cfcPull]
syntax (name := cfcPullTraceConv) "cfc_pull?" optConfig (discharger)? ppSpace colGt
  term:max cfcPullElems (&" only")? (simpArgs)? (" => " colGt tacticSeq)? : conv

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

/-- Replace the placeholders `deferDischarge` left in `proof` by new goals, one per statement. -/
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
classified here, at `high` priority so that it outranks the tagged set. -/
def elabLemmas (only : Bool) (args? : Option (TSyntax ``simpArgs)) : TacticM Lemmas := do
  let all := cfcPullExt.getState (← getEnv)
  let mut state : State := if only then {} else all
  let ctx ← Simp.mkContext (simpTheorems := #[{}])
  let some stx := args? | return { state, ctx }
  let (erase, rest) := stx.raw[1].getSepArgs.partition (·.isOfKind ``simpErase)
  let list := mkNullNode #[mkAtom "[", mkNullNode (mkSepArray rest (mkAtom ",")), mkAtom "]"]
  let res ← elabSimpArgs list ctx #[] (eraseLocal := false) (kind := .simp)
  let mut thms := res.ctx.simpTheorems[0]!
  for (arg, r) in res.simpArgs do
    let #[thm] := r.simpTheorems | continue
    if state.entries.any (·.origin.key == thm.origin.key) then
      thms := thms.eraseCore thm.origin; continue
    let tagged := all.entries.filter (·.origin.key == thm.origin.key)
    let new? ← if !tagged.isEmpty then pure (some tagged) else withRef arg do
      match thm.origin with
      | .decl n .. => mkEntries? (.decl n) (← getConstInfo n).type (eval_prio high)
      | o =>
        mkEntries? o (← inferType thm.proof) (eval_prio high) (some (thm.levelParams, thm.proof))
    let some new := new? | continue
    state := new.foldl (·.add ·) state
    thms := thms.eraseCore thm.origin
  if res.simpArgs.any (·.2 matches .star) then
    for h in ← getPropHyps do
      let some new ← mkEntries? (.fvar h) (← h.getType) (eval_prio high) | continue
      state := new.foldl (·.add ·) state
      thms := thms.eraseCore (.fvar h)
  let mut thmsArray := res.ctx.simpTheorems.set! 0 thms
  for arg in erase do
    let id := arg[1]
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    let o : Origin := .decl declName
    unless state.entries.any (·.origin.key == declName) || thmsArray.any (·.isLemma o) do
      throwErrorAt id "`{.ofConstName declName}` is not in the `cfc_pull` lemma set, so \
        `-{id}` has nothing to remove"
    state := state.erase declName
    thmsArray := thmsArray.map (·.eraseCore o)
  return { state, ctx := res.ctx.setSimpTheorems thmsArray, simprocs := res.simprocs }

/-- Elaborate the arguments of `cfc_pull`. -/
def elabArgs (cfgStx : TSyntax ``optConfig) (only : Bool)
    (lems? : Option (TSyntax ``simpArgs)) (ring : Term) (elems : TSyntax ``cfcPullElems) :
    TacticM (Config × Setup × Array Entry) := do
  let cfg ← elabConfig cfgStx
  let R ← instantiateMVars (← Term.elabType ring)
  -- each is a `group`, of which the term is the last component
  let ts ← elems.raw[0].getArgs.mapM fun g ↦
    Term.elabTermAndSynthesize g[g.getNumArgs - 1] none
  let lems ← elabLemmas only lems?
  let s ← (getSetup ts R).run {
    cfg, lems, disch := deferDischarge !cfg.defer
    cache := ← IO.mkRef #[] }
  return (cfg, s, lems.state.entries)

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
`cfc_tac` for the predicate of the calculus, the discharger `(disch := ..)`, if there is one, for
the goals of no particular kind, and `assumption` for all. -/
def sideGoals (cfg : Config) (disch? : Option (TSyntax ``discharger)) (goals : Array MVarId) :
    TacticM (List MVarId) := do
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
    let mut closed ← tacs.anyM fun tac ↦ do closes g (evalTactic (← `(tactic| (intros; $tac))))
    -- the discharger sees the goal as it is: `intros` would take `f x ≠ 0` apart
    if let some disch := disch? then
      if !closed && !cfg.defer && tag == `cfc_pull.side then
        closed ← closes g (evalTactic disch.raw[3])
    trace[Tactic.cfc_pull] "side goal {ty}: {if closed then "closed" else "unsolved"}"
    unless closed do out := out.push g
  return out.toList

/-- Turn the placeholders in `proof` into side goals and deal with them: those the tactic for
their kind does not close are handed to the `=> ..` block, if there is one. -/
def dischargeSideGoals (cfg : Config) (proof : Expr) (disch? : Option (TSyntax ``discharger))
    (arrow? : Option Syntax)
    (tac? : Option (TSyntax ``tacticSeq)) : TacticM Expr := do
  let (proof, goals) ← replacePlaceholders proof
  let side ← sideGoals cfg disch? goals
  appendGoals side
  if let (some arrow, some tac) := (arrow?, tac?) then
    withRef arrow <| focusGoalsAndDone side.contains (evalTactic tac)
  return proof

@[tactic cfcPull, tactic cfcPullTrace]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let (tk, cfgStx, disch?, only?, lems?, ring, elem, loc?, arrow?, tac?) ← match stx with
    | `(tactic| cfc_pull%$tk $cfgStx:optConfig $[$disch?:discharger]? $ring $elem
        $[only%$only?]? $[$lems?]? $[$loc?:location]? $[=>%$arrow? $tac?]?)
    | `(tactic| cfc_pull?%$tk $cfgStx:optConfig $[$disch?:discharger]? $ring $elem
        $[only%$only?]? $[$lems?]? $[$loc?:location]? $[=>%$arrow? $tac?]?) =>
      pure (tk, cfgStx, disch?, only?, lems?, ring, elem, loc?, arrow?, tac?)
    | _ => throwUnsupportedSyntax
  withRef tk do
  let (cfg, s, entries) ← elabArgs cfgStx only?.isSome lems? ring elem
  let last : Array Syntax := only?.toArray ++ (lems?.map (·.raw)).toArray
  let root ← getMainGoal
  let loc := expandOptLocation (mkOptionalNode loc?)
  let stats ← simpLocation s.ctx s.simprocs s.disch loc
  -- close the goal if it is now `rfl` up to reducible unfolding
  unless (← getGoals).isEmpty do
    if loc matches .wildcard || loc matches .targets _ true then
      evalTactic (← `(tactic| try with_reducible rfl))
  if stx.isOfKind ``cfcPullTrace then
    -- only the part up to the lemma list is replaced, leaving any location and block as written
    let lems ← mkOnlyLemmas stats.usedTheorems entries
    -- a comment after the call is trailing whitespace of its last token
    let elem : TSyntax ``cfcPullElems := ⟨elem.raw.unsetTrailing⟩
    let sugg ← `(tactic| cfc_pull%$tk $cfgStx:optConfig $[$disch?]? $ring $elem only $lems)
    TryThis.addSuggestion tk sugg (origSpan? := mkNullNode (#[tk, elem] ++ last))
  root.assign (← dischargeSideGoals cfg (.mvar root) disch? arrow? tac?)

@[tactic cfcPullConv, tactic cfcPullTraceConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let (tk, cfgStx, disch?, only?, lems?, ring, elem, arrow?, tac?) ← match stx with
    | `(conv| cfc_pull%$tk $cfgStx:optConfig $[$disch?:discharger]? $ring $elem
        $[only%$only?]? $[$lems?]? $[=>%$arrow? $tac?]?)
    | `(conv| cfc_pull?%$tk $cfgStx:optConfig $[$disch?:discharger]? $ring $elem
        $[only%$only?]? $[$lems?]? $[=>%$arrow? $tac?]?) =>
      pure (tk, cfgStx, disch?, only?, lems?, ring, elem, arrow?, tac?)
    | _ => throwUnsupportedSyntax
  withRef tk do
  let (cfg, s, entries) ← elabArgs cfgStx only?.isSome lems? ring elem
  let last : Array Syntax := only?.toArray ++ (lems?.map (·.raw)).toArray
  let lhs ← instantiateMVars (← Conv.getLhs)
  let (r, stats) ← Simp.main lhs s.ctx
    (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
  if r.expr == lhs then throwError "`cfc_pull` made no progress"
  if stx.isOfKind ``cfcPullTraceConv then
    let lems ← mkOnlyLemmas stats.usedTheorems entries
    -- a comment after the call is trailing whitespace of its last token
    let elem : TSyntax ``cfcPullElems := ⟨elem.raw.unsetTrailing⟩
    let sugg ← `(conv| cfc_pull%$tk $cfgStx:optConfig $[$disch?]? $ring $elem only $lems)
    TryThis.addSuggestion tk sugg (origSpan? := mkNullNode (#[tk, elem] ++ last))
  let proof ← dischargeSideGoals cfg (← r.getProof) disch? arrow? tac?
  Conv.applySimpResult { r with proof? := some proof }

end Mathlib.Tactic.CFCPull
