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
  -- `cfc` has 15 arguments and `cfcₙ` has 18; we only rely on the positions of the first three
  -- and the last two, so that the matcher survives a change to the instance arguments.
  guard <| args.size ≥ 5
  return { toExpr := e, unital, ring := args[0]!, alg := args[1]!, pred := args[2]!,
           fn := args[args.size - 2]!, elem := args[args.size - 1]! }

/-- Rebuild the application, replacing the function argument. The other arguments (including the
instances) are reused verbatim, which is the whole point: re-elaborating them would mean
re-running instance synthesis. -/
def CFCApp.withFn (c : CFCApp) (fn : Expr) : CFCApp :=
  let args := c.toExpr.getAppArgs
  { c with toExpr := mkAppN c.toExpr.getAppFn (args.set! (args.size - 2) fn), fn }

/-- Rebuild the application, replacing the element argument. -/
def CFCApp.withElem (c : CFCApp) (elem : Expr) : CFCApp :=
  let args := c.toExpr.getAppArgs
  { c with toExpr := mkAppN c.toExpr.getAppFn (args.set! (args.size - 1) elem), elem }

/-! ### Scalar rings -/

/-- The static approximation of the scalar ring of a tagged lemma.

`RingKey.any` covers both lemmas that are polymorphic over a `CommSemiring`/`CommRing` and
lemmas stated for `RCLike 𝕜`: there is no need to distinguish the two, because a lemma that
cannot be used at a given ring is rejected by instance synthesis when the tactic tries it. -/
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

/-- Whether a lemma with this ring key can be used at the ring `R` *without* a scalar
conversion. -/
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

Such a lemma is an edge `src → tgt` of the scalar conversion graph, running from the ring of its
left-hand side to the ring of its right-hand side. It is only ever used in that direction: the
opposite conversion is a lemma of its own (here `cfc_complex_eq_real`), stated the other way
round and carrying the hypothesis that makes it true. -/
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

/-- A lemma relating the unital and non-unital calculi, i.e. `cfcₙ_eq_cfc`. It is usable in both
directions. -/
structure UnitalLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- The scalar ring of the two `cfc` applications. -/
  ring : RingKey
  /-- Whether the non-unital side is the left-hand side. -/
  nonUnitalOnLhs : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma expressing a composition, e.g. `cfc_comp_pow : cfc (f <| · ^ n) a = cfc f (a ^ n)`.

One side (here the right) has a *structured* element; the other side's element is a bare
variable. `innerHead` is the head symbol of the structured element, which is what the lemma is
indexed by; for `cfc_comp'` it is `cfc` itself. -/
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
  /-- Pull lemmas, indexed by the head of their algebraic side (with holes as wildcards). -/
  pull : DiscrTree PullLemma := {}
  /-- Identity lemmas. -/
  id : Array IdLemma := #[]
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

/-- Remove every entry for `declName` from the database.

Used only by the bracketed lemma list of `cfc_pull`, which modifies the set for a single call;
there is no way to remove a lemma from the database itself. Every category is searched, since
one declaration produces exactly one entry but not always in the category one expects. -/
def Lemmas.erase (s : Lemmas) (declName : Name) : Lemmas where
  -- `DiscrTree` has no `erase`, so the entry is filtered out of every bucket instead; the keys
  -- of an emptied bucket stay in the tree, where they cost a lookup that returns nothing.
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
used, both in left-to-right traversal order.

Subterms containing loose bound variables are never treated as holes; a hole underneath a binder
is fine as long as it does not mention the bound variable, because the caller goes on to abstract
the placeholders into a function and a hole mentioning a bound variable is not a term of the
algebra at all.

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
weaker than it looks; the attribute warns about them.

The test deliberately avoids `isDefEq`, which cannot be run on an expression with loose bound
variables; matching the head constant and the shape of the function argument is enough to
recognise the situation. -/
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

/-- Whether to warn when a `@[cfc_pull]` lemma applies the calculus under a binder, in a
position `cfc_pull` cannot recurse into. Set to `false` when tagging such a lemma on purpose. -/
register_option cfcPull.warnBoundHoles : Bool := {
  defValue := true
  descr := "warn when a `@[cfc_pull]` lemma applies the continuous functional calculus underneath \
    a binder, in a position that `cfc_pull` cannot recurse into"
}

/-! ### Classification -/

/-- Instantiate a tagged lemma: returns its metavariables, their binder infos, the two sides of
the equation and a proof of `lhs = rhs`.

A tagged lemma is always read in the direction it is stated. Every category but `Scalar` is
recognised from whichever side carries the calculus and applied in whichever direction the pull
calls for, so the two readings of the equation coincide; a `Scalar` lemma is an edge of the
conversion graph, and the side it is stated from *is* the direction of that edge. -/
def instantiateLemma (declName : Name) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels declName
  let (mvars, bis, type) ← forallMetaTelescopeReducing (← inferType c)
  let some (_, lhs, rhs) ← matchEq? type |
    throwError "`{ppConst declName}` is not an equation"
  return (mvars, bis, lhs, rhs, mkAppN c mvars)

/-- Build the database entry for `declName`, or throw an informative error explaining why the
lemma cannot be used by `cfc_pull`. -/
def mkEntry (declName : Name) (prio : Nat) : MetaM Entry := do
  let decl := ppConst declName
  let (_, _, lhs, rhs, _) ← instantiateLemma declName
  match CFCApp.match? lhs, CFCApp.match? rhs with
  | none, none =>
    throwError "@[cfc_pull] failed: neither side of `{decl}` has `cfc` or `cfcₙ`\n\
      as its head symbol:{indentD m!"{lhs} = {rhs}"}"
  | some c, none => mkPullEntry c rhs (cfcOnLhs := true)
  | none, some c => mkPullEntry c lhs (cfcOnLhs := false)
  | some cl, some cr => do
    let sameRing ← withNewMCtxDepth <| isDefEq cl.ring cr.ring
    -- if the lhs and rhs are over different scalar rings, then we ensure they both have the
    -- same unitality and enter this as a scalar lemma
    if !sameRing then
      unless cl.unital == cr.unital do
        throwError "@[cfc_pull] failed: `{decl}` changes both the scalar ring and the\n\
          unitality of the functional calculus; such lemmas are not supported."
      -- A `Scalar` lemma is applied by `convert`, which relies on it leaving the element alone;
      -- one that also changes the element would silently produce a result at an element other
      -- than the one being pulled towards. `cfc_comp_re` is the motivating example.
      unless ← withNewMCtxDepth <| isDefEq cl.elem cr.elem do
        throwError "@[cfc_pull] failed: `{decl}` changes both the scalar ring and the\n\
          element of the functional calculus; such lemmas are not supported. A scalar\n\
          conversion must leave the element alone, and a composition must leave the scalar\n\
          ring alone."
      return .scalar
        { declName, src := .ofExpr cl.ring, tgt := .ofExpr cr.ring, unital := cl.unital }
    -- if the lhs and rhs are over the same scalar rings, but have different unitality, we
    -- enter this as a unital lemma
    if cl.unital != cr.unital then
      return .unital { declName, ring := .ofExpr cl.ring, nonUnitalOnLhs := !cl.unital }
    -- same ring, same unitality: this must be a composition lemma
    if ← withNewMCtxDepth <| isDefEq cl.elem cr.elem then
      throwError "@[cfc_pull] failed: both sides of `{decl}` are applications of the same\n\
        functional calculus to the same element; there is nothing for `cfc_pull` to do."
    -- The side to rewrite *from* is the one applying the calculus to the deeper element:
    -- `cfc F a = cfc f (a ^ n)` is used to turn the right-hand side into the left-hand side.
    let srcOnLhs := cl.elem.approxDepth > cr.elem.approxDepth
    if cl.elem.approxDepth == cr.elem.approxDepth then
      throwError "@[cfc_pull] failed: `{decl}` looks like a composition lemma, but neither\n\
        side applies the functional calculus to a more complicated element than the other."
    let src := if srcOnLhs then cl else cr
    let some innerHead := src.elem.getAppFn.constName? |
      throwError "@[cfc_pull] failed: the element `{src.elem}` in `{decl}` has no head\n\
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
      throwError "@[cfc_pull] failed: the non-`cfc` side of `{decl}` is `{alg}`,\n\
        which has no head symbol to index on."
    return .pull
      { declName, prio, ring := .ofExpr c.ring, unital := c.unital, cfcOnLhs,
        numHoles := holes.size }
      keys

/-- The `cfc_pull` attribute marks lemmas for use by the `cfc_pull` tactic.

A tagged lemma must be an equation with `cfc` or `cfcₙ` as the head symbol of at least one side.
It is always read in the direction it is stated: for every category but `Scalar` the direction
makes no difference, and a `Scalar` lemma is an edge of the conversion graph pointing from the
ring of its left-hand side to the ring of its right-hand side.

Examples of lemmas in each of the five categories the attribute recognises:
```
@[cfc_pull] cfc_id'            : cfc (fun x : R ↦ x) a = a
@[cfc_pull] cfc_mul            : cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a
@[cfc_pull] cfc_real_eq_complex: cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a
@[cfc_pull] cfcₙ_eq_cfc        : cfcₙ f a = cfc f a
@[cfc_pull] cfc_comp_pow       : cfc (f <| · ^ n) a = cfc f (a ^ n)
```
-/
syntax (name := cfcPullAttr) "cfc_pull" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  -- The single backtick is required. Attributes live in a flat `Name`-keyed map which
  -- `Lean.Elab.elabAttr` consults under `Name.mkSimple` of the *last component* of the syntax
  -- node kind, so the key here must be the bare `cfcPullAttr`; the resolved name
  -- `Mathlib.Tactic.CFCPull.cfcPullAttr` never matches, and every use of `@[cfc_pull]` then
  -- fails with "Unknown attribute".
  name := `cfcPullAttr
  descr := "lemma used by the `cfc_pull` tactic"
  add := fun declName stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    cfcPullExt.add (← mkEntry declName prio) kind
}

/-- `#cfc_pull_lemmas` displays the contents of the `@[cfc_pull]` database. Useful for
debugging the tactic and its lemma set. -/
elab "#cfc_pull_lemmas" : command => Elab.Command.liftTermElabM do
  let l ← getLemmas
  let sec (header : String) (xs : Array MessageData) : MessageData :=
    if xs.isEmpty then m!"{header}: (none)"
    else m!"{header}:{indentD (MessageData.joinSep xs.toList m!"\n")}"
  logInfo <| MessageData.joinSep [
    sec "identity lemmas" <| l.id.map fun e =>
      m!"{ppConst e.declName} : ring := {e.ring}, unital := {e.unital}",
    sec "pull lemmas" <| l.pull.values.map fun e =>
      m!"{ppConst e.declName} : ring := {e.ring}, unital := {e.unital}, \
        holes := {e.numHoles}, prio := {e.prio}",
    sec "scalar lemmas" <| l.scalar.map fun e =>
      m!"{ppConst e.declName} : {e.src} → {e.tgt}, unital := {e.unital}",
    sec "unital lemmas" <| l.unital.map fun e =>
      m!"{ppConst e.declName} : ring := {e.ring}",
    sec "compose lemmas" <| l.compose.map fun e =>
      m!"{ppConst e.declName} : ring := {e.ring}, unital := {e.unital}, \
        inner := {ppConst e.innerHead}"] m!"\n"

/-- Tracing for the `cfc_pull` tactic. -/
initialize registerTraceClass `Tactic.cfc_pull

end Mathlib.Tactic.CFCPull
