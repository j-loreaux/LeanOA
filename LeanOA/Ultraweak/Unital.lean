import LeanOA.Ultraweak.Basic
import LeanOA.CStarAlgebra.Extreme

/-! # WStarAlgebras are Unital

This may not deserve its own file, but here it is, provisionally.

-/

variable {M P : Type*} [NonUnitalCStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P]
variable [Predual ℂ M P]

open scoped Ultraweak
