module

public import Mathlib.Analysis.CStarAlgebra.Projection

@[expose] public section

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p q : A}

/-- If `p ≤ q` are star projections, then `q * p * q = p`. -/
lemma mul_mul_eq_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ≤ q) :
    q * p * q = p := by
  rw [hp.le_iff_mul_eq_right hq |>.mp h, hp.le_iff_mul_eq_left hq |>.mp h]

end IsStarProjection
