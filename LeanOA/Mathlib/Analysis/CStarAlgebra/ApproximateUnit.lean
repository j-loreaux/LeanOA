import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

open CStarAlgebra Topology Filter

section ApproximateUnit

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

instance [StarOrderedRing A] : (approximateUnit A).NeBot := (increasingApproximateUnit A).neBot

namespace Filter.IsIncreasingApproximateUnit

lemma closedBall_mem {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Metric.closedBall 0 1 ∈ l := by
  simpa [Metric.closedBall] using hl.eventually_norm

lemma nonneg_mem {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    {x | 0 ≤ x} ∈ l := by
  simpa using hl.eventually_nonneg

end Filter.IsIncreasingApproximateUnit

end ApproximateUnit
