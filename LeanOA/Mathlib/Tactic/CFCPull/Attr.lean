/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.DiscrTree.Util

/-!
# The `@[cfc_pull]` attribute

A lemma tagged `@[cfc_pull]` must be an equation in which at least one side has `cfc` or `cfcₙ`
as its head symbol, although for most lemmas it does not matter which. Such a lemma is sorted into
one of five categories, listed below. These lemmas are used by the `cfc_pull` tactic to rewrite
an element of a C⋆-algebra into an application of the continuous functional calculus.

| category  | shape                                              | example              |
| --------- | -------------------------------------------------- | -------------------- |
| `id`      | `cfc (fun x ↦ x) a = a`                           | `cfc_id'`            |
| `pull`    | `cfc f a = ⟨an expression in the algebra⟩`         | `cfc_mul`            |
| `scalar`  | `cfc (f : R → R) a = cfc (g : S → S) a`, `R ≠ S`   | `cfc_real_eq_complex`|
| `unital`  | `cfcₙ f a = cfc f a`                               | `cfcₙ_eq_cfc`        |
| `compose` | `cfc (f ∘ g) a = cfc f ⟨an expression in `a`⟩`     | `cfc_comp_pow`       |

The only lemmas for which the directionality matters are `scalar` lemmas. These lemmas are used by
the tactic to transform switch from a `R`-functional calculus to an `S`-functional calculus.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta

/-! ### Messages -/

/-- A constant, as a message supporting hover and "go to definition". -/
def ppConst (n : Name) : MessageData := .ofConstName n (fullNames := true)

/-! ### Recognising applications of `cfc` and `cfcₙ` -/

/-- The scalar ring and unitality of the relevant continuous functional calculus. -/
structure Mode where
  /-- The scalar ring. -/
  ring : Expr
  /-- `true` for `cfc`, `false` for `cfcₙ`. -/
  unital : Bool
  deriving Inhabited

instance : ToMessageData Mode where
  toMessageData m := m!"{ppConst (if m.unital then ``cfc else ``cfcₙ)} over {m.ring}"

/-- An application `cfc f a` or `cfcₙ f a`, together with the pieces of it that we care about.
We keep the application itself so that we don't need to re-synthesize instance arguments. -/
structure CFCApp extends Mode where
  /-- The application itself, `cfc f a` or `cfcₙ f a`. -/
  toExpr : Expr
  /-- The algebra `A`. -/
  alg : Expr
  /-- The predicate `p : A → Prop` attached to the calculus. -/
  pred : Expr
  /-- The function `f : R → R`. -/
  fn : Expr
  /-- The element `a : A`. -/
  elem : Expr
  deriving Inhabited

/-- Recognise an application of `cfc` or `cfcₙ`. -/
def CFCApp.match? (e : Expr) : Option CFCApp := do
  let .const n _ := e.getAppFn | none
  let unital ←
    if n == ``cfc then pure true
    else if n == ``cfcₙ then pure false
    else none
  let args := e.getAppArgs
  guard <| args.size ≥ 5
  return { toExpr := e, unital, ring := args[0]!, alg := args[1]!, pred := args[2]!,
           fn := args[args.size - 2]!, elem := args[args.size - 1]! }

/-- Replace the function argument of a `cfc` or `cfcₙ` application. -/
def CFCApp.withFn (c : CFCApp) (fn : Expr) : CFCApp :=
  let args := c.toExpr.getAppArgs
  { c with toExpr := mkAppN c.toExpr.getAppFn (args.set! (args.size - 2) fn), fn }

/-- Replace the element argument of a `cfc` or `cfcₙ` application. -/
def CFCApp.withElem (c : CFCApp) (elem : Expr) : CFCApp :=
  let args := c.toExpr.getAppArgs
  { c with toExpr := mkAppN c.toExpr.getAppFn (args.set! (args.size - 1) elem), elem }

/-! ### Scalar rings -/

/-- A representation of the scalar ring of a lemma tagged `@[cfc_pull]`. -/
inductive RingKey where
  /-- The lemma is about a fixed ring, with the given head constant (e.g. `Real`). -/
  | const (n : Name)
  /-- The lemma is polymorphic in its scalar ring. -/
  | any
  deriving Inhabited, BEq, Repr, DecidableEq

instance : ToMessageData RingKey where
  toMessageData
    | .const n => ppConst n
    | .any => m!"_"

/-- The `RingKey` of an expression denoting a scalar ring.

This is only ever called on the `CFCApp.ring` of after having matched with `CFCApp.match?` -/
def RingKey.ofExpr (R : Expr) : RingKey :=
  match R.getAppFn with
  | .const n _ => .const n
  | _ => .any

/-- Whether a lemma with this ring key can be used at the ring `R` *without* a scalar conversion. -/
def RingKey.matchesRing (k : RingKey) (R : Expr) : MetaM Bool := do
  match k with
  | .any => return true
  | .const n => return (← whnfR R).getAppFn.constName? == some n

/-! ### Lemma records -/

/-- A lemma of the form `cfc (fun x ↦ x) a = a`, used as the base case of the recursion. -/
structure IdLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The scalar ring of the `cfc` application. -/
  ring : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the `cfc` side is the left-hand side. -/
  cfcOnLhs : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma with `cfc`/`cfcₙ` on one side and an algebraic expression on the other, e.g.
`cfc_mul : cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a`.

The subterms of the algebraic side which are themselves `cfc`/`cfcₙ` applications at the same
ring, unitality and element (here `cfc f a` and `cfc g a`) are called *holes*: they are the
positions at which the tactic recurses. -/
structure PullLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The attribute priority. -/
  prio : Nat
  /-- The scalar ring of the `cfc` application. -/
  ring : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the `cfc` side is the left-hand side. -/
  cfcOnLhs : Bool
  /-- The number of holes on the algebraic side. -/
  numHoles : Nat
  deriving Inhabited, BEq, Repr

/-- A lemma relating the calculus over two different scalar rings, e.g.
`cfc_real_eq_complex : cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a`.
Such a lemma is an edge `src → tgt` of the scalar conversion graph, going from left to right. -/
structure ScalarLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The ring converted *from*. -/
  src : RingKey
  /-- The ring converted *to*. -/
  tgt : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma relating the unital and non-unital calculi, i.e. `cfcₙ_eq_cfc`. -/
structure UnitalLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The scalar ring of the two `cfc` applications. -/
  ring : RingKey
  /-- Whether the non-unital side is the left-hand side. -/
  nonUnitalOnLhs : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma expressing a composition, e.g. `cfc_comp_pow : cfc (f <| · ^ n) a = cfc f (a ^ n)`.
One side has a *structured* element of the algebra, whose head symbol is this `innerHead`. -/
structure ComposeLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The attribute priority. -/
  prio : Nat
  /-- The scalar ring of the two `cfc` applications. -/
  ring : RingKey
  /-- Whether the lemmas are about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the side with the structured element is the left-hand side. -/
  srcOnLhs : Bool
  /-- The head symbol of the structured element. -/
  innerHead : Name
  deriving Inhabited, BEq, Repr

/-- An entry added to the `cfc_pull` database. -/
inductive Entry where
  /-- An identity lemma. -/
  | id (l : IdLemma)
  /-- A pull lemma, together with its `DiscrTree` keys. -/
  | pull (l : PullLemma) (keys : Array DiscrTree.Key)
  /-- A scalar conversion lemma. -/
  | scalar (l : ScalarLemma)
  /-- A unitality conversion lemma. -/
  | unital (l : UnitalLemma)
  /-- A composition lemma. -/
  | compose (l : ComposeLemma)
  deriving Inhabited

/-- The `cfc_pull` lemma database. -/
structure Lemmas where
  /-- Identity lemmas. -/
  id : Array IdLemma := #[]
  /-- Pull lemmas, indexed by the head of their algebraic side (with holes as wildcards). -/
  pull : DiscrTree PullLemma := {}
  /-- Scalar conversion lemmas, viewed as the edges of a graph on ring keys. -/
  scalar : Array ScalarLemma := #[]
  /-- Unitality conversion lemmas. -/
  unital : Array UnitalLemma := #[]
  /-- Composition lemmas. -/
  compose : Array ComposeLemma := #[]
  deriving Inhabited

/-- Add an entry to the database. -/
def Lemmas.addEntry (s : Lemmas) : Entry → Lemmas
  | .id l => { s with id := s.id.push l }
  | .pull l keys => { s with pull := s.pull.insertKeyValue keys l }
  | .scalar l => { s with scalar := s.scalar.push l }
  | .unital l => { s with unital := s.unital.push l }
  | .compose l => { s with compose := s.compose.push l }

/-- Whether the database has an entry for `declName`. -/
def Lemmas.contains (s : Lemmas) (declName : Name) : Bool :=
  s.pull.values.any (·.declName == declName) || s.id.any (·.declName == declName) ||
    s.scalar.any (·.declName == declName) || s.unital.any (·.declName == declName) ||
    s.compose.any (·.declName == declName)

/-- Temporarily remove an entry for `declName` from the database. Only used when passing a list
of lemmas to `cfc_pull` in brackets, e.g. `cfc_pull [-lemma1, -lemma2]`. -/
def Lemmas.erase (s : Lemmas) (declName : Name) : Lemmas where
  pull := s.pull.mapArrays (·.filter (·.declName != declName))
  id := s.id.filter (·.declName != declName)
  scalar := s.scalar.filter (·.declName != declName)
  unital := s.unital.filter (·.declName != declName)
  compose := s.compose.filter (·.declName != declName)

/-- The environment extension holding the `@[cfc_pull]` lemmas. -/
initialize cfcPullExt : SimpleScopedEnvExtension Entry Lemmas ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := Lemmas.addEntry
  }

/-- The `@[cfc_pull]` lemmas available in the current environment. -/
def getLemmas : CoreM Lemmas := return cfcPullExt.getState (← getEnv)

/-! ### Finding and abstracting holes -/

/-- Replace every maximal subterm of `e` satisfying `isHole` by a fresh placeholder produced by
`mk`. Returns the resulting pattern together with the replaced subterms and the placeholders
used, both in left-to-right traversal order. Subterms containing loose bound variables are never
treated as holes.

The traversal is written out rather than delegated to `Meta.transform` for two reasons, both to
do with that loose-bound-variable test: `Meta.transform` instantiates binders with local
hypotheses before visiting a body, so the test would never fire and a hole could capture a
variable that does not exist outside the traversal; and it memoises on structural equality, which
would give two structurally equal holes the same placeholder. -/
partial def abstractHoles (isHole : Expr → MetaM Bool) (mk : MetaM Expr) (e : Expr) :
    MetaM (Expr × Array Expr × Array Expr) := do
  let (pat, (holes, phs)) ← (go e).run (#[], #[])
  return (pat, holes, phs)
where
  /-- The traversal. It stops at the outermost hole, which is what makes the holes maximal. -/
  go (e : Expr) : StateT (Array Expr × Array Expr) MetaM Expr := do
    if !e.hasLooseBVars then
      if ← isHole e then
        let ph ← mk
        modify fun (hs, ps) => (hs.push e, ps.push ph)
        return ph
    match e with
    | .app f x => return .app (← go f) (← go x)
    | .lam n t b bi => return .lam n (← go t) (← go b) bi
    | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
    | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
    | .mdata d b => return .mdata d (← go b)
    | .proj s i b => return .proj s i (← go b)
    | _ => return e

/-- Test whether `s` is a hole relative to the `cfc` application `ref`: an application of the
same calculus, at the same ring and element, whose function argument is a variable in the sense
of `isVar`. -/
def isHoleFor (ref : CFCApp) (isVar : Expr → MetaM Bool) (s : Expr) : MetaM Bool := do
  let some c := CFCApp.match? s | return false
  unless c.unital == ref.unital do return false
  unless ← isVar c.fn do return false
  withNewMCtxDepth do
    unless ← isDefEq c.ring ref.ring do return false
    unless ← isDefEq c.elem ref.elem do return false
    return true

/-- The subterms of `alg` that *would* be holes relative to `ref` were it not for the bound
variables they mention. `abstractHoles` skips these, so a lemma containing one is usable but
weaker than it looks; the attribute warns about them. -/
def boundHoles (ref : CFCApp) (alg : Expr) : MetaM (Array Expr) := do
  let acc ← IO.mkRef (#[] : Array Expr)
  alg.forEach' fun e => do
    if e.hasLooseBVars then
      if let some c := CFCApp.match? e then
        if c.unital == ref.unital && c.fn.getAppFn.isMVar then
          acc.modify (·.push e)
          -- do not descend: a partial application of `cfc` inside a full one is not a
          -- separate hole
          return false
    return true
  acc.get

/-- Warn when a `@[cfc_pull]` lemma applies the calculus under a binder. -/
register_option cfcPull.warnBoundHoles : Bool := {
  defValue := true
  descr := "Warn when a `@[cfc_pull]` lemma applies the calculus under a binder."
}

/-! ### Classification -/

/-- Instantiate a tagged lemma: returns its metavariables, their binder infos, the two sides of
the equation and a proof of `lhs = rhs`. -/
def instantiateLemma (declName : Name) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels declName
  let (mvars, bis, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, lhs, rhs) ← matchEq? type |
    throwError "`{ppConst declName}` is not an equation"
  return (mvars, bis, lhs, rhs, mkAppN c mvars)

/-- Categorize a declaration with the necessary information for `cfc_pull`. -/
def mkEntry (declName : Name) (prio : Nat) : MetaM Entry := do
  let decl := ppConst declName
  let (_, _, lhs, rhs, _) ← instantiateLemma declName
  match CFCApp.match? lhs, CFCApp.match? rhs with
  | none, none =>
    throwError "`@[cfc_pull]` failed: neither side of `{decl}` has `cfc` or `cfcₙ`\n\
      as its head symbol:{indentD m!"{lhs} = {rhs}"}"
  -- only one side has `cfc` or `cfcₙ` as its head symbol → pull lemma
  | some c, none => mkPullEntry c rhs (cfcOnLhs := true)
  | none, some c => mkPullEntry c lhs (cfcOnLhs := false)
  | some cl, some cr => do
    let sameRing ← withNewMCtxDepth <| isDefEq cl.ring cr.ring
    -- different scalar rings, same unitality → scalar lemma
    if !sameRing then
      unless cl.unital == cr.unital do
        throwError "`@[cfc_pull]` failed: `{decl}` changes both the scalar ring and the\n\
          unitality of the functional calculus; such lemmas are not supported."
      unless ← withNewMCtxDepth <| isDefEq cl.elem cr.elem do
        throwError "`@[cfc_pull]` failed: `{decl}` changes both the scalar ring and the\n\
          element of the functional calculus; such lemmas are not supported."
      return .scalar
        { declName, src := .ofExpr cl.ring, tgt := .ofExpr cr.ring, unital := cl.unital }
    -- same scalar ring, but different unitality → unital lemma
    if cl.unital != cr.unital then
      return .unital { declName, ring := .ofExpr cl.ring, nonUnitalOnLhs := !cl.unital }
    -- same ring, same unitality → composition lemma
    if ← withNewMCtxDepth <| isDefEq cl.elem cr.elem then
      throwError "`@[cfc_pull]` failed: both sides of `{decl}` are applications of the same\n\
        functional calculus to the same element; there is nothing for `cfc_pull` to do."
    -- determine which side to rewrite from by deciding which has a the more complicated term.
    let srcOnLhs := cl.elem.approxDepth > cr.elem.approxDepth
    if cl.elem.approxDepth == cr.elem.approxDepth then
      throwError "`@[cfc_pull]` failed: `{decl}` looks like a composition lemma, but neither\n\
        side applies the functional calculus to a more complicated element than the other."
    let src := if srcOnLhs then cl else cr
    let some innerHead := src.elem.getAppFn.constName? |
      throwError "`@[cfc_pull]` failed: the element `{src.elem}` in `{decl}` has no head\n\
        constant to index on."
    return .compose
      { declName, prio, ring := .ofExpr cl.ring, unital := cl.unital, srcOnLhs, innerHead }
where
  /-- Classify a lemma with a `cfc` application on exactly one side. -/
  mkPullEntry (c : CFCApp) (alg : Expr) (cfcOnLhs : Bool) : MetaM Entry := do
    let decl := ppConst declName
    if ← withNewMCtxDepth <| isDefEq alg c.elem then
      return .id { declName, ring := .ofExpr c.ring, unital := c.unital, cfcOnLhs }
    let isVar (e : Expr) : MetaM Bool := return e.isMVar
    let (pat, holes, _) ← abstractHoles (isHoleFor c isVar) (mkFreshExprMVar c.alg) alg
    for b in ← boundHoles c alg do
      unless cfcPull.warnBoundHoles.get (← getOptions) do continue
      logWarning m!"`{decl}` applies the functional calculus at{indentExpr b}\n\
        which mentions a bound variable. `cfc_pull` cannot recurse under a binder, so it will\n\
        treat that position as part of the pattern rather than as a hole: the lemma will only\n\
        apply when the position is already an application of the calculus.\n\
        \n\
        If that is what you intend, silence this warning with\n\
        `set_option cfcPull.warnBoundHoles false in`."
    let keys ← DiscrTree.mkPath pat
    if keys.size ≤ 1 then
      throwError "`@[cfc_pull]` failed: the non-`cfc` side of `{decl}` is `{alg}`,\n\
        which has no head symbol to index on."
    return .pull
      { declName, prio, ring := .ofExpr c.ring, unital := c.unital, cfcOnLhs,
        numHoles := holes.size }
      keys

/-- The `cfc_pull` attribute marks lemmas for use by the `cfc_pull` tactic and categorizes them
based on their purpose. Such lemmas are used by the tactic to rewrite an element of a C⋆-algebra
into an application of the continuous functional calculus.

A tagged lemma must be an equation with `cfc` or `cfcₙ` as the head symbol of at least one side.
The five categories the recognized by the attribute are:

| category  | shape                                              | example              |
| --------- | -------------------------------------------------- | -------------------- |
| `id`      | `cfc (fun x ↦ x) a = a`                           | `cfc_id'`            |
| `pull`    | `cfc f a = ⟨an expression in the algebra⟩`         | `cfc_mul`            |
| `scalar`  | `cfc (f : R → R) a = cfc (g : S → S) a`, `R ≠ S`   | `cfc_real_eq_complex`|
| `unital`  | `cfcₙ f a = cfc f a`                               | `cfcₙ_eq_cfc`        |
| `compose` | `cfc (f ∘ g) a = cfc f ⟨an expression in `a`⟩`     | `cfc_comp_pow`       |
-/
syntax (name := cfcPullAttr) "cfc_pull" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `cfcPullAttr
  descr := "lemma used by the `cfc_pull` tactic"
  add := fun declName stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    cfcPullExt.add (← mkEntry declName prio) kind
}

/-- Tracing for the `cfc_pull` tactic. -/
initialize registerTraceClass `Tactic.cfc_pull

end Mathlib.Tactic.CFCPull
