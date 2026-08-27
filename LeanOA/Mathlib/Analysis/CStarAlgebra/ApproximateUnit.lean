module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

@[expose] public section

open CStarAlgebra Topology Filter

section ApproximateUnit

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

instance [StarOrderedRing A] : (approximateUnit A).NeBot := (increasingApproximateUnit A).neBot

namespace Filter.IsIncreasingApproximateUnit

lemma nonneg_mem {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    {x | 0 ≤ x} ∈ l := by
  simpa using! hl.eventually_nonneg

end Filter.IsIncreasingApproximateUnit

end ApproximateUnit
