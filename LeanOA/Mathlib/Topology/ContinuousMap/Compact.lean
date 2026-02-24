import Mathlib.Topology.ContinuousMap.Compact
import LeanOA.Mathlib.Topology.ContinuousMap.Bounded.Normed

variable {X R : Type*} [TopologicalSpace X] [NormedRing R] [IsDomain R]

open BoundedContinuousFunction in
lemma ContinuousMap.norm_add_eq_max [CompactSpace X] {f g : C(X, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using congr($h x)
  simpa using BoundedContinuousFunction.norm_add_eq_max h
