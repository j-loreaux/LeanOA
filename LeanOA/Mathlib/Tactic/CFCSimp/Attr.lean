module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Lean.Meta.Tactic.Simp

/-!
# The `@[cfc_simp]` attribute

A lemma tagged `@[cfc_simp]` is an equation with `cfc` or `cfcₙ` at the head of at least one side.
The attribute sorts it into one of the kinds below and records, alongside, the orientation in which
`simp` should use it (towards the calculus), its scalar ring and unitality, and whether its
algebraic side contains applications of the calculus (*holes*).

| kind      | shape                                                   | example               |
| --------- | ------------------------------------------------------- | --------------------- |
| `pull`    | `cfc f a = ⟨an expression in the algebra⟩`              | `cfc_mul`             |
| `target`  | a `pull` lemma whose algebraic side does not fix `R`    | `cfc_id'`             |
| `conv`    | `cfc (f : R → R) a = cfc (g : S → S) a`, `cfcₙ f a = cfc f a` | `cfcₙ_eq_cfc`   |
| `compose` | `cfc (f ∘ g) a = cfc f ⟨an expression in `a`⟩`          | `cfc_comp_pow`        |

The lemmas are used as they are, hypotheses included: `cfc_simp`'s discharger defers those it
cannot prove as side goals.
-/

public meta section

namespace Mathlib.Tactic.CFCSimp

open Lean Meta

/-- What a tagged lemma is for. -/
inductive Kind where
  /-- `⟨algebraic expression⟩ = cfc f a`, usable as a plain `simp` lemma. -/
  | pull
  /-- Like `pull`, but the ring (and so the element) is not determined by the algebraic side,
  e.g. `a = cfc (fun x : R ↦ x) a`. `cfc_simp` instantiates these at its targets. -/
  | target
  /-- `cfc f ⟨structured element⟩ = cfc g a`, e.g. `cfc f (CFC.abs a) = cfc (f ‖·‖) a`. -/
  | compose
  /-- `cfc f a = cfc g a` changing the scalar ring or the unitality. -/
  | conv
  deriving Inhabited, BEq, Repr

/-- A tagged lemma, in one of the orientations `cfc_simp` may use it in. -/
structure Entry where
  /-- The lemma: a declaration, or, from the `[..]` list of `cfc_simp`, a local hypothesis. -/
  origin : Origin
  /-- Whether `simp` uses it right to left. -/
  inv : Bool
  /-- Its kind. -/
  kind : Kind
  /-- The attribute priority. -/
  prio : Nat
  /-- The head constant of the scalar ring of the right-hand side (as `simp` sees it), if it is
  concrete. -/
  ring : Option Name
  /-- Whether the right-hand side (as `simp` sees it) is `cfc` rather than `cfcₙ`. -/
  unital : Bool
  /-- For `conv` lemmas: the ring of the left-hand side. -/
  srcRing : Option Name := none
  /-- For `conv` lemmas: the unitality of the left-hand side. -/
  srcUnital : Bool := true
  /-- For `pull` and `target` lemmas: whether the algebraic side has applications of the calculus
  in it (*holes*). A lemma without holes is applied top-down, before its argument is simplified. -/
  holes : Bool := true
  deriving Inhabited

/-- The environment extension holding the `@[cfc_simp]` lemmas. -/
initialize cfcSimpExt : SimpleScopedEnvExtension Entry (Array Entry) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := Array.push }

/-- Recognise `cfc f a` or `cfcₙ f a`: `(ring, unital, fn, elem)`. -/
def matchCFC? (e : Expr) : Option (Expr × Bool × Expr × Expr) := do
  let .const n _ := e.getAppFn | none
  let unital ← if n == ``cfc then pure true else if n == ``cfcₙ then pure false else none
  let args := e.getAppArgs
  guard <| args.size ≥ 5
  return (args[0]!, unital, args[args.size - 2]!, args[args.size - 1]!)

/-- The head constant of a ring, if concrete. -/
def ringKey (R : Expr) : Option Name := R.getAppFn.constName?

/-- The lemma as a term, with fresh universe metavariables. -/
def Entry.proof (e : Entry) : MetaM Expr :=
  match e.origin with
  | .decl n .. => mkConstWithFreshMVarLevels n
  | .fvar id => return mkFVar id
  | _ => do throwError "internal error: `cfc_simp` entry with origin `{← ppOrigin e.origin}`"

/-- Add the lemma to a simp set, in its orientation. -/
def Entry.addTo (e : Entry) (s : SimpTheorems) (prio : Nat := e.prio) : MetaM SimpTheorems :=
  match e.origin with
  | .decl n .. => s.addConst n (inv := e.inv) (prio := prio)
  | .fvar id => s.add e.origin #[] (mkFVar id) (inv := e.inv) (prio := prio)
  | _ => do throwError "internal error: `cfc_simp` entry with origin `{← ppOrigin e.origin}`"

/-- Classify a lemma of type `type`: the entries recording how `cfc_simp` may use it. -/
def mkEntries (origin : Origin) (type : Expr) (prio : Nat) : MetaM (Array Entry) := do
  forallTelescopeReducing type fun xs body => do
    let some (_, lhs, rhs) := body.eq? |
      throwError "`cfc_simp`: `{← ppOrigin origin}` is not an equation"
    match matchCFC? lhs, matchCFC? rhs with
    | none, none =>
      throwError "`cfc_simp`: neither side of `{← ppOrigin origin}` has `cfc` or `cfcₙ` as \
        its head symbol"
    | some c, none => pullEntry xs rhs lhs c true
    | none, some c => pullEntry xs lhs rhs c false
    | some (Rl, ul, _, el), some (Rr, ur, _, er) =>
      if el == er then
        -- a conversion; record both directions, `cfc_simp` picks one
        return #[
          { origin, inv := false, kind := .conv, prio, ring := ringKey Rr, unital := ur,
            srcRing := ringKey Rl, srcUnital := ul },
          { origin, inv := true, kind := .conv, prio, ring := ringKey Rl, unital := ul,
            srcRing := ringKey Rr, srcUnital := ur }]
      else
        -- a composition: the side whose element is more complicated goes on the left
        let inv := el.approxDepth < er.approxDepth
        let (R, u) := if inv then (Rl, ul) else (Rr, ur)
        return #[{ origin, inv, kind := .compose, prio, ring := ringKey R, unital := u }]
where
  /-- A lemma with the calculus on exactly one side, `cfcSide`; `inv` says it is the left one. -/
  pullEntry (xs : Array Expr) (alg cfcSide : Expr) (c : Expr × Bool × Expr × Expr) (inv : Bool) :
      MetaM (Array Entry) := do
    let (R, unital, _, _) := c
    -- a type only determined by instances that are not `outParam`s cannot be found by `simp`
    let freeType ← xs.anyM fun x => do
      return (← isType x) && !alg.containsFVar x.fvarId! && !cfcSide.containsFVar x.fvarId!
    let kind := if R.isFVar && !alg.containsFVar R.fvarId! || freeType then .target else .pull
    let holes := (alg.find? fun e ↦ (matchCFC? e).isSome).isSome
    return #[{ origin, inv, kind, prio, ring := ringKey R, unital, holes }]

/-- The `cfc_simp` attribute marks lemmas for use by the `cfc_simp` tactic; see the module
docstring for the shapes it accepts. -/
syntax (name := cfcSimpAttr) "cfc_simp" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `cfcSimpAttr
  descr := "lemma used by the `cfc_simp` tactic"
  add := fun declName stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    for e in ← mkEntries (.decl declName) (← getConstInfo declName).type prio do
      cfcSimpExt.add e kind
}

/-- Tracing for the `cfc_simp` tactic. -/
initialize registerTraceClass `Tactic.cfc_simp

end Mathlib.Tactic.CFCSimp
