import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped NNReal

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

namespace CFC

-- should replace this upstream
-- this proof doesn't require `[IsTopologicalRing A]`
lemma sqrt_mul_sqrt_self' (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt a * sqrt a = a := by
  simp [CFC.sqrt, ← cfcₙ_mul NNReal.sqrt NNReal.sqrt a, ← sq, cfcₙ_id' ℝ≥0 a]

end CFC
