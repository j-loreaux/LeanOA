import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions

theorem ExtremallyDisconnected_of_Blah {I} [PartialOrder I] [IsDirectedOrder I] (x : I → C(K, ℝ))
    (hfmono : Monotone x)
    (hsup_of_bdd : Set.Bounded (α := C(K, ℝ)) LE.le {x i | i : I} → SupSet {x i | i : I})
    : ExtremallyDisconnected K :=
  by sorry
