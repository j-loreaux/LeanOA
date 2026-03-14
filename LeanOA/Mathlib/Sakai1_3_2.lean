import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions

theorem ExtremallyDisconnected_of_Monotone_ConditionallyCompletePartialOrderSup
    : (∀ I [PartialOrder I] [IsDirectedOrder I], ∀ x : I → C(K, ℝ),
      Monotone x → ConditionallyCompletePartialOrderSup {x i | i : I}) → ExtremallyDisconnected K :=
  by sorry
