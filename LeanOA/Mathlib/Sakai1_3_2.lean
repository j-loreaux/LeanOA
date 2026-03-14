import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions

/- The following is wrong because it must be true for every x with these properties and
every I, not just one of them-/
theorem ExtremallyDisconnected_of_Monotone_ConditionallyCompletePartialOrderSup
    {I} [PartialOrder I] [IsDirectedOrder I] (x : I → C(K, ℝ))
    (hfmono : Monotone x) (hcc : ConditionallyCompletePartialOrderSup {x i | i : I})
    : ExtremallyDisconnected K :=
  by sorry
