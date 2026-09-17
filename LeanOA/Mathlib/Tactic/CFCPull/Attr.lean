module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Lean.Meta.Tactic.Simp

/-!
# The `@[cfc_pull]` attribute

The `cfc_pull` attribute marks lemmas for use by the `cfc_pull` tactic and categorizes them
according to their shape, and records other information used by the tactic.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta

/-- What a tagged lemma is for. -/
inductive Kind where
  /-- `⟨algebraic expression⟩ = cfc f a`, usable as a plain `simp` lemma. -/
  | pull
  /-- Like `pull`, but the ring, the element or a type is not determined by the algebraic side,
  e.g. `a = cfc (fun x : R ↦ x) a`, so `simp` cannot use the lemma as it is. `cfc_pull`
  specializes these at the ring asked for and, if need be (`Entry.elemFree`), at its targets. -/
  | target
  /-- `cfc f ⟨structured element⟩ = cfc g a`, e.g. `cfc f (CFC.abs a) = cfc (f ‖·‖) a`. -/
  | compose
  /-- `cfc f a = cfc g a` changing the scalar ring or the unitality. -/
  | conv
  deriving Inhabited, BEq, Repr

/-- A tagged lemma, in one of the orientations `cfc_pull` may use it in. -/
structure Entry where
  /-- The lemma: a declaration, or, from the `[..]` list of `cfc_pull`, a local hypothesis (`*`)
  or a term. -/
  origin : Origin
  /-- The proof and its universe parameters, as `simp` elaborated them, when the lemma is a term
  from the `[..]` list of `cfc_pull`. -/
  term? : Option (Array Name × Expr) := none
  /-- Whether `simp` uses it right to left. -/
  inv : Bool
  /-- Its `CFCPUll.Kind`: `pull`, `target`, `compose` or `conv`. -/
  kind : Kind
  /-- The attribute priority. -/
  prio : Nat
  /-- The head constant of the scalar ring of the right-hand side, if it is
  concrete. -/
  ring : Option Name
  /-- Whether the right-hand side is `cfc` rather than `cfcₙ`. -/
  unital : Bool
  /-- For `conv` lemmas: the ring of the left-hand side. -/
  srcRing : Option Name := none
  /-- For `conv` lemmas: the unitality of the left-hand side. -/
  srcUnital : Bool := true
  /-- For `pull` and `target` lemmas: whether the algebraic side has applications of the calculus
  in it (*holes*). A lemma without holes is applied top-down, before its argument is simplified. -/
  holes : Bool := true
  /-- For `target` lemmas: whether some type appears in neither side of the equation, like the `S`
  of `StarAlgHomClass.map_cfc`. `cfc_pull` has to guess it, and tries the scalar rings it knows. -/
  freeType : Bool := false
  /-- For `target` lemmas: whether the element has to be supplied, because the algebraic side is
  the bare element (`a = cfc (fun x ↦ x) a`, which would match anything) or does not mention it
  (`1 = cfc (fun _ ↦ 1) a`). Otherwise `simp` finds the element by unification, and `cfc_pull`
  accepts the rewrite if it is a target. -/
  elemFree : Bool := false
  /-- For `pull` and `target` lemmas: the head constant of the element the calculus is applied to,
  if it is structured: `DFunLike.coe` for the `φ a` of `φ (cfc f a) = cfc f (φ a)`. -/
  elemHead : Option Name := none
  /-- The lemma as `simp` uses it, in its orientation and at its priority, if `simp` can use it on
  its own, finding the ring and the element by unification: that is, unless it is a `target`
  lemma, which `cfc_pull` specializes when it is called. -/
  thms : Array SimpTheorem := #[]
  deriving Inhabited

/-- What the lemmas of a simp set of `cfc_pull` are for. -/
inductive SetKind where
  /-- `pull` lemmas with holes: `simp` uses them itself. -/
  | pull
  /-- `pull` lemmas with holes towards a structured element (`φ (cfc f a) = cfc f (φ a)`), used
  only if that element is a target. -/
  | towards
  /-- `pull` lemmas without holes, at a concrete ring (`CFC.sqrt a = cfc √· a`): used top-down. -/
  | loose
  /-- `pull` lemmas without holes that are generic in their ring, which they find in a scalar
  (`r • a = cfc (r * ·) a`): used top-down, if `r` is in the ring asked for and `a` is a target. -/
  | looseTowards
  /-- `compose` lemmas. -/
  | compose
  /-- `conv` lemmas, in one direction. -/
  | conv
  deriving Inhabited, BEq, Repr

/-- The lemmas of one simp set have the same use, ring and unitality. `cfc_pull` orders the sets
for one use when it knows which ring and unitality are asked for: fewer scalar conversions first,
then the requested unitality. Inside a set the priority decides, as always. -/
structure Key where
  /-- The use. -/
  set : SetKind
  /-- The head constant of the scalar ring, if it is concrete. -/
  ring : Option Name
  /-- Whether the calculus is `cfc` rather than `cfcₙ`. -/
  unital : Bool
  /-- For `conv` lemmas: the ring converted from. -/
  srcRing : Option Name := none
  /-- For `conv` lemmas: the unitality converted from. -/
  srcUnital : Bool := true
  deriving Inhabited, BEq

/-- The simp set a lemma goes to when it is tagged, if it is not one `cfc_pull` specializes. -/
def Entry.key? (e : Entry) : Option Key :=
  let set? : Option SetKind := match e.kind with
    | .target => none
    | .compose => some .compose
    | .conv => some .conv
    | .pull => some <|
      if e.holes then (if e.elemHead.isSome then .towards else .pull)
      else if e.ring.isNone then .looseTowards else .loose
  set?.map fun set ↦
    { set, ring := e.ring, unital := e.unital, srcRing := e.srcRing, srcUnital := e.srcUnital }

/-- The `@[cfc_pull]` lemmas, and the simp sets of those `simp` can use on its own. -/
structure State where
  /-- The lemmas. -/
  entries : Array Entry := #[]
  /-- The simp sets. -/
  sets : Array (Key × SimpTheorems) := #[]
  deriving Inhabited

/-- Add lemmas to a simp set. -/
def State.insert (s : State) (k : Key) (thms : Array SimpTheorem) : State :=
  let add (t : SimpTheorems) := thms.foldl (·.addSimpTheorem ·) t
  match s.sets.findIdx? (·.1 == k) with
  | some i => { s with sets := s.sets.modify i fun (k, t) ↦ (k, add t) }
  | none => { s with sets := s.sets.push (k, add {}) }

/-- Add a lemma, to its simp set too if it has one. -/
def State.add (s : State) (e : Entry) : State :=
  let s := { s with entries := s.entries.push e }
  match e.key? with
  | some k => s.insert k e.thms
  | none => s

/-- Remove the lemmas of a declaration. -/
def State.erase (s : State) (declName : Name) : State :=
  let (gone, entries) := s.entries.partition (·.origin.key == declName)
  let origins := gone.flatMap (·.thms.map (·.origin))
  { entries, sets := s.sets.map fun (k, t) ↦ (k, origins.foldl (·.eraseCore ·) t) }

/-- The environment extension holding the `@[cfc_pull]` lemmas. -/
initialize cfcPullExt : SimpleScopedEnvExtension Entry State ←
  registerSimpleScopedEnvExtension { initial := {}, addEntry := State.add }

/-- Recognise `cfc f a` or `cfcₙ f a`: `(ring, unital, fn, elem)`. -/
def matchCFC? (e : Expr) : Option (Expr × Bool × Expr × Expr) := do
  let .const n _ := e.getAppFn | none
  let unital ← if n == ``cfc then pure true else if n == ``cfcₙ then pure false else none
  let args := e.getAppArgs
  guard <| args.size ≥ 5
  return (args[0]!, unital, args[args.size - 2]!, args[args.size - 1]!)

/-- The lemma as a term, with fresh universe metavariables. -/
def Entry.proof (e : Entry) : MetaM Expr := do
  if let some (ps, prf) := e.term? then
    return prf.instantiateLevelParamsArray ps (← ps.mapM fun _ ↦ mkFreshLevelMVar)
  match e.origin with
  | .decl n .. => mkConstWithFreshMVarLevels n
  | .fvar id => return mkFVar id
  | _ => do throwError "internal error: `cfc_pull` entry with origin `{← ppOrigin e.origin}`"

/-- Classify a lemma of type `type`: the entries recording how `cfc_pull` may use it, or `none`
if it is not an equation with `cfc` or `cfcₙ` at the head of a side. -/
def mkEntries? (origin : Origin) (type : Expr) (prio : Nat)
    (term? : Option (Array Name × Expr) := none) : MetaM (Option (Array Entry)) := do
  forallTelescopeReducing type fun xs body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let entries ← match matchCFC? lhs, matchCFC? rhs with
    | none, none => return none
    | some c, none => pullEntry xs rhs lhs c true
    | none, some c => pullEntry xs lhs rhs c false
    | some (Rl, ul, _, el), some (Rr, ur, _, er) =>
      if el == er then
        if ul == ur && Rl == Rr then
          throwError "`cfc_pull`: both sides of `{← ppOrigin origin}` are the same calculus \
            applied to the same element; there is nothing for `cfc_pull` to do with it"
        -- a conversion; record both directions, `cfc_pull` picks one
        pure #[
          { origin, inv := false, kind := .conv, prio, ring := Rr.getAppFn.constName?, unital := ur,
            srcRing := Rl.getAppFn.constName?, srcUnital := ul },
          { origin, inv := true, kind := .conv, prio, ring := Rl.getAppFn.constName?, unital := ul,
            srcRing := Rr.getAppFn.constName?, srcUnital := ur }]
      else
        -- a composition: the side whose element is more complicated goes on the left
        let inv := el.approxDepth < er.approxDepth
        let (R, u) := if inv then (Rl, ul) else (Rr, ur)
        pure #[
          { origin, inv, kind := .compose, prio, ring := R.getAppFn.constName?, unital := u }]
    entries.mapM fun e ↦ do
      let e := { e with term? }
      if e.kind == Kind.target then return e
      -- what `simp` makes of the lemma, once and for all
      let thms ← match origin, term? with
        | _, some (ps, prf) => mkSimpTheoremFromExpr origin ps prf (inv := e.inv) (prio := prio)
        | .decl n .., _ => mkSimpTheoremFromConst n (inv := e.inv) (prio := prio)
        | .fvar id, _ => mkSimpTheoremFromExpr origin #[] (mkFVar id) (inv := e.inv) (prio := prio)
        | _, _ => throwError "internal error: `cfc_pull` lemma `{← ppOrigin origin}`"
      return { e with thms }
where
  /-- A lemma with the calculus on exactly one side, `cfcSide`; `inv` says it is the left one. -/
  pullEntry (xs : Array Expr) (alg cfcSide : Expr) (c : Expr × Bool × Expr × Expr) (inv : Bool) :
      MetaM (Array Entry) := do
    let (R, unital, _, elem) := c
    -- a type only determined by instances that are not `outParam`s cannot be found by `simp`
    let freeType ← xs.anyM fun x => do
      return (← isType x) && !alg.containsFVar x.fvarId! && !cfcSide.containsFVar x.fvarId!
    -- the ring, or the element (`cfc_const : cfc (fun _ ↦ r) a = algebraMap R A r`), may be
    -- absent from the algebraic side too
    let free (x : Expr) := x.isFVar && !alg.containsFVar x.fvarId!
    let kind := if free R || free elem || freeType then .target else .pull
    let holes := (alg.find? fun e ↦ (matchCFC? e).isSome).isSome
    let ring := R.getAppFn.constName?
    let elemHead := elem.getAppFn.constName?
    let elemFree := elem.isFVar && (alg == elem || !alg.containsFVar elem.fvarId!)
    return #[{ origin, inv, kind, prio, ring, unital, holes, freeType, elemHead, elemFree }]

/-- Classify a lemma of type `type`, which must be one `cfc_pull` can use. -/
def mkEntries (origin : Origin) (type : Expr) (prio : Nat) : MetaM (Array Entry) := do
  let some entries ← mkEntries? origin type prio |
    throwError "`cfc_pull`: `{← ppOrigin origin}` is not an equation with `cfc` or `cfcₙ` as the \
      head symbol of a side"
  return entries

/-- The `cfc_pull` attribute marks lemmas for use by the `cfc_pull` tactic. Such a lemma is
an equation with `cfc` or `cfcₙ` at the head of at least one side. The attribute sorts lemmas
into the following categories and records other information used by the tactic, including
the scalar ring, unitality, and whether the algebraic side contains applications of `cfc` (*holes*).

| category  | shape                                                   | example               |
| --------- | ------------------------------------------------------- | --------------------- |
| `pull`    | `cfc f a = ⟨an expression in the algebra⟩`              | `cfc_mul`             |
| `target`  | a `pull` lemma whose algebraic side does not fix `R`    | `cfc_id'`             |
| `conv`    | `cfc (f : R → R) a = cfc (g : S → S) a`, `cfcₙ f a = cfc f a` | `cfcₙ_eq_cfc`   |
| `compose` | `cfc (f ∘ g) a = cfc f ⟨an expression in `a`⟩`          | `cfc_comp_pow`        |
-/
syntax (name := cfcPullAttr) "cfc_pull" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `cfcPullAttr
  descr := "lemma used by the `cfc_pull` tactic"
  add := fun declName stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    for e in ← mkEntries (.decl declName) (← getConstInfo declName).type prio do
      cfcPullExt.add e kind
}

/-- Tracing for the `cfc_pull` tactic. -/
initialize registerTraceClass `Tactic.cfc_pull

end Mathlib.Tactic.CFCPull
