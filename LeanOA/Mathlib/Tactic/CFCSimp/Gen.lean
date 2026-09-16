module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Lean.Meta.Tactic.Simp
public meta import Lean.Elab.Command

/-!
# Experiment: `cfc_pull` via `simp`, the lemma database

**This is an experiment.** `cfc_simp_gen foo` takes a `cfc_pull` lemma `foo` and adds a copy
`CFCSimp.foo`, proved by `sorry`, with every hypothesis the statement does not mention removed and
oriented in the *pull* direction (the algebraic side on the left, the calculus on the right). The
copy is recorded, with its kind, for the `cfc_simp` tactic.

Removing the hypotheses models a `simp` discharger that always succeeds, which is exactly the
question being asked: how close does `simp` get to `cfc_pull` if side goals are no obstacle?
-/

public meta section

namespace Mathlib.Tactic.CFCSimp

open Lean Meta Elab Command

/-- What a generated lemma is for. -/
inductive Kind where
  /-- `⟨algebraic expression⟩ = cfc f a`, usable as a plain `simp` lemma. -/
  | pull
  /-- Like `pull`, but the ring (and so the element) is not determined by the left-hand side,
  e.g. `a = cfc (fun x : R ↦ x) a`. `cfc_simp` instantiates these at its targets. -/
  | target
  /-- `cfc f ⟨structured element⟩ = cfc g a`, e.g. `cfc f (CFC.abs a) = cfc (f ‖·‖) a`. -/
  | compose
  /-- `cfc f a = cfc g a` changing the scalar ring or the unitality. -/
  | conv
  deriving Inhabited, BEq, Repr

/-- A generated lemma. -/
structure Entry where
  /-- The `sorry`d declaration. -/
  declName : Name
  /-- Its kind. -/
  kind : Kind
  /-- The priority it was generated with. -/
  prio : Nat
  /-- The head constant of the scalar ring of the right-hand side, if it is concrete. -/
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
  /-- The original lemma. -/
  origName : Name := .anonymous
  /-- Whether this copy is the original read right to left. -/
  inv : Bool := false
  deriving Inhabited

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

/-- Add `CFCSimp.{declName}{suffix} : ∀ xs, lhs = rhs`, proved by `sorry`, keeping only the binders
among `xs` that the statement (or a kept binder) mentions, or that are not propositions. -/
def addSorryDecl (declName : Name) (suffix : String) (lvls : List Name) (xs : Array Expr)
    (lhs rhs : Expr) : MetaM Name := do
  let body ← mkEq lhs rhs
  -- walk the binders right to left, keeping those still needed
  let mut kept : Array Expr := #[]
  let mut needed := body
  for x in xs.reverse do
    let decl ← x.fvarId!.getDecl
    let isPropHyp := !decl.binderInfo.isInstImplicit && (← isProp decl.type)
    if isPropHyp && !needed.containsFVar x.fvarId! then
      continue
    kept := kept.push x
    needed := mkApp needed decl.type
  kept := kept.reverse
  let type ← mkForallFVars kept body
  let type ← instantiateMVars type
  let name := (`CFCSimp ++ declName).appendAfter suffix
  addDecl <| .thmDecl { name, levelParams := lvls, type, value := ← mkSorry type false }
  return name

/-- Generate the `sorry`d copies of a `cfc_pull` lemma and record them. -/
def generate (declName : Name) (prio : Nat) : MetaM (Array Entry) := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "`{declName}` is not an equation"
    let lvls := info.levelParams
    match matchCFC? lhs, matchCFC? rhs with
    | none, none => throwError "`{declName}`: neither side is `cfc`/`cfcₙ`"
    | some c, none => pullEntry lvls xs rhs lhs c true
    | none, some c => pullEntry lvls xs lhs rhs c false
    | some (Rl, ul, _, el), some (Rr, ur, _, er) =>
      if el == er then
        -- a conversion; record both directions, `cfc_simp` picks one
        let n₁ ← addSorryDecl declName "" lvls xs lhs rhs
        let n₂ ← addSorryDecl declName "_symm" lvls xs rhs lhs
        return #[
          { declName := n₁, kind := .conv, prio, ring := ringKey Rr, unital := ur,
            srcRing := ringKey Rl, srcUnital := ul, origName := declName },
          { declName := n₂, kind := .conv, prio, ring := ringKey Rl, unital := ul,
            srcRing := ringKey Rr, srcUnital := ur, origName := declName, inv := true }]
      else
        -- a composition: the side whose element is more complicated goes on the left
        let inv := el.approxDepth < er.approxDepth
        let (l, r, R, u) := if !inv then (lhs, rhs, Rr, ur) else (rhs, lhs, Rl, ul)
        let n ← addSorryDecl declName "" lvls xs l r
        let entry : Entry :=
          { declName := n, kind := .compose, prio := prio, ring := ringKey R, unital := u
            origName := declName, inv := inv }
        return #[entry]
where
  pullEntry (lvls : List Name) (xs : Array Expr) (alg cfcSide : Expr)
      (c : Expr × Bool × Expr × Expr) (inv : Bool) : MetaM (Array Entry) := do
    let (R, unital, _, _) := c
    let n ← addSorryDecl declName "" lvls xs alg cfcSide
    -- if the ring is a variable that the algebraic side does not mention, `simp` cannot use it
    -- likewise if some other type is only determined by instances that are not `outParam`s
    let freeType ← xs.anyM fun x => do
      return (← isType x) && !alg.containsFVar x.fvarId! && !cfcSide.containsFVar x.fvarId!
    let kind := if R.isFVar && !alg.containsFVar R.fvarId! || freeType then .target else .pull
    let holes := (alg.find? fun e ↦ (matchCFC? e).isSome).isSome
    let entry : Entry :=
      { declName := n, kind := kind, prio := prio, ring := ringKey R, unital := unital
        holes := holes, origName := declName, inv := inv }
    return #[entry]

/-- `cfc_simp_gen (prio)? foo bar ..`: generate the `sorry`d, hypothesis-free, pull-direction copies
`CFCSimp.foo`, `CFCSimp.bar`, .. of `cfc_pull` lemmas, for use by `cfc_simp`. -/
elab "cfc_simp_gen" p:(prio)? ids:(ppSpace ident)+ : command => do
  let prio ← match p with
    | some p => liftMacroM <| evalPrio p
    | none => pure (eval_prio default)
  for id in ids do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let entries ← liftTermElabM <| generate declName prio
    for e in entries do
      cfcSimpExt.add e

end Mathlib.Tactic.CFCSimp
