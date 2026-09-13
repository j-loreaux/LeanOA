/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Init
public import Lean.Elab.Tactic.Basic

/-!
# Additions to `Lean.Elab.Tactic.Basic`

`focusGoals` and `focusGoalsAndDone` generalize `focus` and `focusAndDone` from the main goal to
any selection of the goals in the goal list.
-/

@[expose] public section

open Lean Elab Tactic

namespace Lean.Elab.Tactic

/-- Runs `x` with only the unsolved goals satisfying `select` as the goal list, in their original
order. The goals `x` leaves are placed at the front of the goal list, followed by the goals that
were not selected. Goals satisfying `select` that are not in the goal list are not added to it. -/
def focusGoals {α} (select : MVarId → Bool) (x : TacticM α) : TacticM α := do
  let (selected, rest) := (← getUnsolvedGoals).partition select
  setGoals selected
  let a ← x
  setGoals ((← getUnsolvedGoals) ++ rest)
  pure a

/-- Runs `x` with only the unsolved goals satisfying `select` as the goal list, and expects it to
leave no goals. The goals that were not selected are restored afterwards. -/
def focusGoalsAndDone {α} (select : MVarId → Bool) (x : TacticM α) : TacticM α :=
  focusGoals select do
    let a ← x
    done
    pure a

end Lean.Elab.Tactic
