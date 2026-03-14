import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K] [T2Space K] [CompactSpace K]

open ContinuousFunctions

theorem ExtremallyDisconnected_of_ConditionallyCompletePartialOrderSup
    : ConditionallyCompletePartialOrderSup {f : C(K, ℝ) | ∀ x, 0 ≤ f x} →
    ExtremallyDisconnected K :=
  by sorry
