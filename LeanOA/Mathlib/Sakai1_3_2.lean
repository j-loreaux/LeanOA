import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions

theorem ExtremallyDisconnected_of_ConditionallyCompletePartialOrderSup
    : ConditionallyCompletePartialOrderSup C(K, ℂ) → ExtremallyDisconnected K :=
  by sorry
