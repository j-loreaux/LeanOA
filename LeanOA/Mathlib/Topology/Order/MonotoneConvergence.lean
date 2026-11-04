module

public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

open Filter Topology

variable {α β : Type*} [Preorder α] [Preorder β] [TopologicalSpace β] [SupConvergenceClass β]
  {f : α → β} {d : Set α} {a : α}

/-- If `f` is Scott continuous on `D` and monotone on a nonempty directed set `d ∈ D` with least
upper bound `a`, then `f` tends to `f a` along `d`. -/
theorem ScottContinuousOn.tendsto_atTop_isLUB {D : Set (Set α)} (hf : ScottContinuousOn D f)
    (hd : d ∈ D) (hne : d.Nonempty) (hdir : DirectedOn (· ≤ ·) d) (hmono : MonotoneOn f d)
    (ha : IsLUB d a) : Tendsto (fun x : d ↦ f x) atTop (𝓝 (f a)) := by
  refine _root_.tendsto_atTop_isLUB (fun x y hxy ↦ hmono x.2 y.2 hxy) ?_
  rw [← Set.image_eq_range]
  exact hf hd hne hdir ha

/-- If `f` is Scott continuous, then `f` tends to `f a` along any nonempty directed set `d` with
least upper bound `a`. -/
theorem ScottContinuous.tendsto_atTop_isLUB (hf : ScottContinuous f) (hne : d.Nonempty)
    (hdir : DirectedOn (· ≤ ·) d) (ha : IsLUB d a) :
    Tendsto (fun x : d ↦ f x) atTop (𝓝 (f a)) :=
  hf.scottContinuousOn.tendsto_atTop_isLUB (Set.mem_univ d) hne hdir (hf.monotone.monotoneOn d) ha
