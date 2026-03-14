import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions NNReal

theorem ExtremallyDisconnected_of_ConditionallyCompletePartialOrderSup
    : ConditionallyCompletePartialOrderSup C(K, ℝ≥0) → ExtremallyDisconnected K :=
  by sorry
