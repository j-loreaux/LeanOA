module

public import LeanOA.Mathlib.Tactic.CFCSimp.Attr
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Parser.Tactic
public meta import Lean.Elab.Tactic.Conv.Basic
public meta import Lean.Elab.Tactic.Conv.Simp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public meta import LeanOA.Mathlib.Lean.Elab.Tactic.Basic

/-!
# `cfc_pull` via `simp`

`cfc_simp R a` is `simp only` with the `@[cfc_simp]` lemmas, plus what cannot be expressed without
knowing `R` and `a`:

* *targets*: `a`, and the outermost subterms of `a` in other algebras (`x` in `φ x`, in `↑x`);
* the `target` lemmas (`a = cfc id a`, `1 = cfc 1 a`, `star b = cfc star b`, ..), instantiated at
  `R` (and, when the left-hand side is the bare element, at the target);
* priorities, boosted for lemmas at the ring `R` and the requested unitality;
* one simproc on `cfc f b` / `cfcₙ f b`, which converts the scalar ring and unitality towards the
  requested ones (conversion lemmas are included only in that direction, so they cannot loop),
  applies composition lemmas, and simplifies `b` (never `f`), unless `b` is a target.

The lemmas are the real ones, hypotheses included. `simp` rejects a rewrite whose proof contains
an assignable metavariable, so the discharger cannot leave a goal behind; instead it fills each
hypothesis it cannot prove with a marked placeholder, which the tactic turns into a side goal once
`simp` is done (`deferDischarge`, `replacePlaceholders`). The side goals then get the treatment
`cfc_pull` gives them: the tactic for their kind, or the `=> ..` block.
-/

public meta section

namespace Mathlib.Tactic.CFCSimp

open Lean Meta Elab Tactic Parser.Tactic

/-- Configuration for `cfc_simp`. -/
structure Config where
  /-- Prefer the unital calculus. -/
  unital : Bool := true
  /-- Unfold `let`-bound local variables. -/
  zetaDelta : Bool := false
  /-- Hand every side goal to the `=> ..` block, attempting none. -/
  defer : Bool := false

declare_config_elab elabConfig Config

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
  try
    let p ← mkFreshExprMVar (← mkArrow alg (.sort .zero))
    let cls ← mkClassApp
      (if unital then ``ContinuousFunctionalCalculus else ``NonUnitalContinuousFunctionalCalculus)
      #[R, alg, p]
    return (← trySynthInstance cls).toOption.isSome
  catch _ => return false

/-- The target at `s`, if its type has a calculus over `R`. -/
def mkTarget? (cfg : Config) (R s : Expr) : MetaM (Option Target) := do
  let alg ← instantiateMVars (← inferType s)
  if cfg.unital && (← hasCFC true R alg) then return some { elem := s, alg, unital := true }
  if ← hasCFC false R alg then return some { elem := s, alg, unital := false }
  return none

/-- The targets: `t` itself, and, as in `cfc_pull`, the elements that the holes of a lemma with a
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
        let (_, _, ty) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels
          e.declName))
        let some (_, lhs, rhs) := ty.eq? | return #[]
        let some (_, _, _, elem) := matchCFC? rhs | return #[]
        if elem.isMVar then return #[]
        unless ← withReducible <| isDefEq elem t do return #[]
        let mut found := #[]
        let holes ← IO.mkRef #[]
        (← instantiateMVars lhs).forEach fun h ↦ do
          if let some (_, _, _, b) := matchCFC? h then
            unless b.hasMVar || b.hasLooseBVars do holes.modify (·.push b)
        for b in ← holes.get do found := found.push b
        return found
      for b in found do
        if ← out.anyM fun o ↦ return o.elem == b then continue
        if let some tg ← mkTarget? cfg R b then
          out := out.push tg; todo := todo.push b
    go out todo

/-- Priority adjusted for the requested ring and unitality: as in `cfc_pull`, fewer scalar
conversions first, then the right unitality, then the priority. -/
def boost (dist : Option Name → Option Nat) (unital : Bool) (e : Entry) : Nat :=
  let conversions := match e.ring with
    | none => 0
    | some n => (dist (some n)).getD 9
  e.prio + 20000 * (10 - conversions) + (if e.unital == unital then 10000 else 0)

/-- Distances from the key of `R` in the graph of scalar conversions. -/
def ringDistances (R : Expr) (entries : Array Entry) : Array (Name × Nat) := Id.run do
  let some r := ringKey R | return #[]
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

/-- Set the binder infos of the leading lambdas of `e`. -/
def setBinderInfos : Expr → List BinderInfo → Expr
  | .lam n t b _, bi :: bis => .lam n t (setBinderInfos b bis) bi
  | e, _ => e

/-- Instantiate a `target` lemma at `R` and a target: its ring is `R`, and its element is the
target itself if the left-hand side is the bare element, or else any element of the target's
algebra. -/
def instantiateTarget (R : Expr) (t : Target) (e : Entry) (S : Expr := R) :
    MetaM (Option (Expr × Bool)) := do
  unless e.unital == t.unital do return none
  let c ← mkConstWithFreshMVarLevels e.declName
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
  -- instances that can be found now are; the others stay binders for `simp` to synthesize
  for (m, bi) in mvars.zip bis do
    if bi.isInstImplicit && (← instantiateMVars m).isMVar then
      let ty ← instantiateMVars (← inferType m)
      unless ty.hasExprMVar do
        let some inst ← (try some <$> synthInstance ty catch _ => pure none) | return none
        unless ← isDefEq m inst do return none
  -- abstract what is left, keeping the binder infos
  let mut rest := #[]
  let mut restBis := #[]
  for (m, bi) in mvars.zip bis do
    let m ← instantiateMVars m
    if m.isMVar then rest := rest.push m; restBis := restBis.push bi
  let body := mkAppN c mvars
  let body ← if e.inv then mkEqSymm body else pure body
  let prf ← mkLambdaFVars rest (← instantiateMVars body)
  let prf := setBinderInfos prf restBis.toList
  return some (prf, lhs.isMVar)

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
  targets.anyM fun t => do
    if e == t.elem then return true
    unless e.getAppFn == t.elem.getAppFn && e.getAppNumArgs == t.elem.getAppNumArgs do
      return false
    withNewMCtxDepth <| withReducible <| isDefEq e t.elem

/-- Replace the `i`th argument of `e` by the result `r` of simplifying it. -/
def congrAt (e : Expr) (i : Nat) (r : Simp.Result) : MetaM Simp.Result := do
  let args := e.getAppArgs
  let some h := r.proof? | return { expr := mkAppN e.getAppFn (args.set! i r.expr) }
  let motive ← withLocalDeclD `y (← inferType args[i]!) fun y =>
    mkLambdaFVars #[y] (mkAppN e.getAppFn (args.set! i y))
  return { expr := mkAppN e.getAppFn (args.set! i r.expr), proof? := ← mkCongrArg motive h }

mutual

/-- The simp context and simprocs pulling towards `R`, cached per ring. -/
partial def getSetup (cfg : Config) (t : Expr) (entries : Array Entry) (disch : Simp.Discharge)
    (cache : IO.Ref (Array (Expr × Setup))) (stack : IO.Ref (Array Expr)) (R : Expr) :
    MetaM Setup := do
  for (R', s) in ← cache.get do
    if ← withNewMCtxDepth <| isDefEq R R' then return s
  let targets ← findTargets cfg entries R t
  let dist := ringDistances R entries
  let distOf (n : Option Name) : Option Nat := n.bind fun n ↦ (dist.find? (·.1 == n)).map (·.2)
  -- a concrete ring that is not a node of the conversion graph is only usable if it is `R`
  let distOf (n : Option Name) : Option Nat :=
    if n == ringKey R then some 0 else distOf n
  let mut pull : SimpTheorems := {}
  let mut loose : SimpTheorems := {}
  let mut conv : SimpTheorems := {}
  let mut flip : SimpTheorems := {}
  let mut compose : SimpTheorems := {}
  let mut tgt : SimpTheorems := {}
  let mut atom : SimpTheorems := {}
  for n in [``eq_self, ``iff_self] do
    pull ← pull.addConst n
  for e in entries do
    let (name, inv) := (e.declName, e.inv)
    match e.kind with
    | .pull =>
      if e.holes then pull ← pull.addConst name (inv := inv) (prio := boost distOf cfg.unital e)
      else loose ← loose.addConst name (inv := inv) (prio := boost distOf cfg.unital e)
    | .compose =>
      compose ← compose.addConst name (inv := inv) (prio := boost distOf cfg.unital e)
    | .conv =>
      if e.unital != e.srcUnital then
        flip ← flip.addConst name (inv := inv)
        -- towards the requested unitality
        if e.unital == cfg.unital then conv ← conv.addConst name (inv := inv) (prio := 2000)
      else if let (some d, some d') := (distOf e.ring, distOf e.srcRing) then
        -- towards the requested ring
        if d < d' then conv ← conv.addConst name (inv := inv)
    | .target =>
      for (tg, i) in targets.zipIdx do
        let mut seen : Array Expr := #[]
        -- the rings of the conversion graph, all of which are constants
        for S in #[R] ++ dist.map (mkConst ·.1) do
          let some (prf, bare) ← instantiateTarget R tg e S | continue
          let r ← abstractMVars prf
          if seen.contains r.expr then continue
          seen := seen.push r.expr
          trace[Tactic.cfc_simp] "{e.declName} at {tg.elem}: {← inferType prf}"
          let id := .other (e.declName ++ `inst)
          if bare then
            atom ← atom.add id r.paramNames r.expr
          else if e.holes then
            tgt ← tgt.add id r.paramNames r.expr
              (prio := 100000 + boost distOf cfg.unital e - 100 * i)
          else
            loose ← loose.add id r.paramNames r.expr
              (prio := boost distOf cfg.unital e - 100 * i)
  let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta } (simpTheorems := #[pull, tgt])
  let procs := getSetup cfg t entries disch cache stack
  let simprocs : Simp.Simprocs := {
    pre := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcSimpPre, post := false, keys := #[.star],
        proc := .inl (cfcPre R targets atom loose conv compose stack procs) }
    post := DiscrTree.empty.insertKeyValue #[.star]
      { declName := `cfcSimpFlip, post := true, keys := #[.star],
        proc := .inl (flipPost flip #[pull, tgt]) } }
  let s := { ctx, simprocs := #[simprocs], disch }
  cache.modify (·.push (R, s))
  return s

/-- The pre-simproc. A target is wrapped as `cfc id a` before `simp` can look inside it. On
`cfc f b`: compose; simplify `b` (never `f`) unless it is a target, at the ring of this `cfc` if
that is not the requested one, so that an inner element is pulled at the ring of the calculus
applied to it; and only then convert towards the requested unitality, then ring. -/
partial def cfcPre (R : Expr) (targets : Array Target) (atom loose conv compose : SimpTheorems)
    (stack : IO.Ref (Array Expr)) (setup : Expr → MetaM Setup) : Simp.Simproc := fun e => do
  let some (S, _, _, b) := matchCFC? e |
    if ← isTargetElem targets e then
      if let some r ← Simp.rewrite? e atom.post atom.erased "cfc_simp atom" false then
        return .visit r
      return .continue
    if let some r ← Simp.rewrite? e loose.post loose.erased "cfc_simp loose" false then
      return .visit r
    return .continue
  unless e.getAppNumArgs == (← getConstInfo e.getAppFn.constName!).type.getForallArity do
    return .continue
  let isTarget ← isTargetElem targets b
  unless isTarget do
    if let some r ← Simp.rewrite? e compose.post compose.erased "cfc_simp compose" false then
      return .visit r
  -- an element already being simplified further up is left alone, or `ψ a ↦ cfc id (ψ a)` loops
  if !isTarget && !(← stack.get).contains b then
    stack.modify (·.push b)
    let rb ← try
        if ← withNewMCtxDepth <| isDefEq S R then Simp.simp b else do
          let s ← setup S
          let (rb, _) ← Simp.main b s.ctx
            (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
          pure rb
      finally stack.modify (·.pop)
    -- `cfc id b`, say, is no progress: composing would give `e` back, and loop
    let same := match matchCFC? rb.expr with
      | some (_, _, _, b') => b' == b
      | none => false
    if rb.expr != b && !same then
      return .visit (← Simp.mkCongrArg e.appFn! rb)
  if let some r ← Simp.rewrite? e conv.post conv.erased "cfc_simp conv" false then
    return .visit r
  return .done { expr := e }

/-- The post-simproc, run when no lemma applies to `e`: flip the unitality of an argument that is an
application of the calculus, and try the lemmas again. -/
partial def flipPost (flip : SimpTheorems) (thms : Array SimpTheorems) : Simp.Simproc := fun e => do
  if (matchCFC? e).isSome then return .continue
  let args := e.getAppArgs
  for h : i in [0:args.size] do
    let arg := args[i]
    unless (matchCFC? arg).isSome do continue
    let some r ← Simp.rewrite? arg flip.post flip.erased "cfc_simp flip" false | continue
    let r₁ ← congrAt e i r
    for s in thms do
      if let some r₂ ← Simp.rewrite? r₁.expr s.post s.erased "cfc_simp" false then
        return .visit (← r₁.mkEqTrans r₂)
  return .continue

end

/-- The lemma list of `cfc_simp`. -/
syntax cfcSimpLemmas := " [" withoutPosition(ident,*,?) "]"

/-- `cfc_simp R a`: a `simp`-based `cfc_pull R a`. Rewrites the goal (or the location `at ..`)
so that the calculus over `R` is at the head of every maximal subexpression in the algebra of
`a`, using the `@[cfc_simp]` lemmas together with those in `[..]`. Side goals are attempted with
the tactic for their kind, as in `cfc_pull`, and the survivors are handed to the `=> ..` block, or
left open; `+defer` attempts none of them. `-unital` asks for `cfcₙ`; `+zetaDelta` unfolds
`let`-bound variables. -/
syntax (name := cfcSimp) "cfc_simp" optConfig (cfcSimpLemmas)? ppSpace colGt term:max ppSpace
  colGt term:max (location)? (" => " colGt tacticSeq)? : tactic

@[inherit_doc cfcSimp]
syntax (name := cfcSimpConv) "cfc_simp" optConfig (cfcSimpLemmas)? ppSpace colGt term:max ppSpace
  colGt term:max (" => " colGt tacticSeq)? : conv

/-- Discharge a hypothesis with a local hypothesis if there is one, and otherwise with a
placeholder. `simp` rejects a rewrite whose proof contains an assignable metavariable, so the
placeholder is a `sorry`, marked so that `replacePlaceholders` can turn it into a goal
afterwards. -/
def deferDischarge (useHyps : Bool) : Simp.Discharge := fun e => do
  let e ← instantiateMVars e
  let e := if e.isAppOfArity ``autoParam 2 then e.appFn!.appArg! else e
  if e.hasExprMVar then return none
  -- a class about types (`NonUnitalAlgHomClass F S A B`) is for instance synthesis, which has
  -- already failed; a class about an element (`IsStarNormal a`) is a side goal like any other
  if (← isClass? e).isSome then
    if ← e.getAppArgs.allM fun x ↦ isType x <||> return (← isClass? (← inferType x)).isSome then
      return none
  for d in ← getLCtx do
    unless useHyps do break
    if d.isImplementationDetail then continue
    if ← withReducible <| isDefEq d.type e then return some d.toExpr
  return some <| .mdata (KVMap.empty.insert `cfcSimpSideGoal (.ofBool true)) (← mkSorry e true)

/-- Replace the placeholders `deferDischarge` left in `proof` by new goals, one per statement. -/
def replacePlaceholders (proof : Expr) : MetaM (Expr × Array MVarId) := do
  let proof ← instantiateMVars proof
  let found ← IO.mkRef (#[] : Array (Expr × Expr))
  proof.forEach fun e => do
    if let .mdata d b := e then
      if d.contains `cfcSimpSideGoal then
        let ty ← inferType b
        unless (← found.get).any (·.1 == ty) do
          found.modify (·.push (ty, ← mkFreshExprSyntheticOpaqueMVar ty))
  let found ← found.get
  let proof := proof.replace fun e => match e with
    | .mdata d b => if d.contains `cfcSimpSideGoal then
        found.find? (·.1 == b.appFn!.appArg!) |>.map (·.2) else none
    | _ => none
  return (proof, found.map (·.2.mvarId!))

/-- Elaborate the arguments of `cfc_simp`. -/
def elabArgs (cfgStx : TSyntax ``optConfig) (lems? : Option (TSyntax ``cfcSimpLemmas))
    (ring elem : Term) : TacticM (Config × Setup) := do
  let cfg ← elabConfig cfgStx
  let R ← instantiateMVars (← Term.elabType ring)
  let t ← Term.elabTerm elem none
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t
  let mut entries := cfcSimpExt.getState (← getEnv)
  if let some stx := lems? then
    for id in stx.raw[1].getSepArgs do
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      if entries.any (·.declName == declName) then continue
      entries := entries ++ (← withRef id <| mkEntries declName (eval_prio default))
  let s ← getSetup cfg t entries (deferDischarge !cfg.defer) (← IO.mkRef #[]) (← IO.mkRef #[]) R
  return (cfg, s)

/-- The side goals, deduplicated, and without those the tactics of `cfc_pull` close. -/
def sideGoals (cfg : Config) (goals : Array MVarId) : TacticM (List MVarId) := do
  let mut out : Array MVarId := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if let some g' ← out.findM? fun g' => do withReducible <| isDefEq ty (← g'.getType) then
      g.assign (mkMVar g'); continue
    -- as in `cfc_pull`, the tactic is chosen by the kind of goal, and other goals are left alone
    let isNonneg := match ty.le? with
      | some (_, lhs, _) => lhs.zero?
      | none => false
    let mentions (n : Name) := (ty.find? (·.isConstOf n)).isSome
    let (tag, tacs) ← if ty.isAppOf ``IsSelfAdjoint || ty.isAppOf ``IsStarNormal || isNonneg then
        pure (`cfc_pull.predicate, ← [`(tactic| assumption), `(tactic| exact cfc_predicate _ _),
          `(tactic| exact cfcₙ_predicate _ _), `(tactic| cfc_tac)].mapM id)
      else if mentions ``Continuous || mentions ``ContinuousOn then
        pure (`cfc_pull.continuity, ← [`(tactic| assumption), `(tactic| cfc_cont_tac)].mapM id)
      else if ty.eq?.any (·.2.2.zero?) then
        pure (`cfc_pull.mapZero, ← [`(tactic| assumption), `(tactic| cfc_zero_tac)].mapM id)
      else
        pure (`cfc_pull.side, ← [`(tactic| assumption), `(tactic| exact cfc_predicate _ _),
          `(tactic| exact cfcₙ_predicate _ _)].mapM id)
    g.setTag tag
    let tacs := if cfg.defer then [] else tacs
    let mut closed := false
    for tac in tacs do
      let saved ← saveState
      -- runtime exceptions too: `cfc_zero_tac` can loop, on `0 = f 0` say
      let ok ← Term.withoutErrToSorry <| tryCatchRuntimeEx
        (do pure (← Tactic.run g (evalTactic tac)).isEmpty) fun _ => pure false
      if ok then closed := true; break
      saved.restore
    trace[Tactic.cfc_simp] "side goal {ty}: {if closed then "closed" else "left"}"
    unless closed do out := out.push g
  return out.toList

@[tactic cfcSimp]
def evalCFCSimp : Tactic := fun stx => withMainContext do
  let `(tactic| cfc_simp $cfgStx:optConfig $[$lems?]? $ring $elem $[$loc?]? $[=>%$arrow? $tac?]?) :=
    stx | throwUnsupportedSyntax
  let (cfg, s) ← elabArgs cfgStx lems? ring elem
  let root ← getMainGoal
  let loc := expandOptLocation (mkOptionalNode loc?)
  _ ← simpLocation s.ctx s.simprocs s.disch loc
  -- as `cfc_pull` does, close the goal if it is now `rfl` up to reducible unfolding
  unless (← getGoals).isEmpty do
    if loc matches .wildcard || loc matches .targets _ true then
      try evalTactic (← `(tactic| with_reducible rfl)) catch _ => pure ()
  let (proof, goals) ← replacePlaceholders (mkMVar root)
  root.assign proof
  let side ← sideGoals cfg goals
  appendGoals side
  if let (some arrow, some tac) := (arrow?, tac?) then
    withRef arrow <| focusGoalsAndDone side.contains (evalTactic tac)

@[tactic cfcSimpConv]
def evalCFCSimpConv : Tactic := fun stx => withMainContext do
  let `(conv| cfc_simp $cfgStx:optConfig $[$lems?]? $ring $elem $[=>%$arrow? $tac?]?) := stx
    | throwUnsupportedSyntax
  let (cfg, s) ← elabArgs cfgStx lems? ring elem
  let lhs ← instantiateMVars (← Conv.getLhs)
  let (r, _) ← Simp.main lhs s.ctx
    (methods := Simp.mkMethods s.simprocs s.disch (wellBehavedDischarge := false))
  if r.expr == lhs then throwError "`cfc_simp` made no progress"
  let (proof, goals) ← replacePlaceholders (← r.getProof)
  Conv.applySimpResult { r with proof? := some proof }
  let side ← sideGoals cfg goals
  appendGoals side
  if let (some arrow, some tac) := (arrow?, tac?) then
    withRef arrow <| focusGoalsAndDone side.contains (evalTactic tac)

end Mathlib.Tactic.CFCSimp
