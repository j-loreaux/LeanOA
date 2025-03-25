/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Results for `Abs` that require CStarAlgebra instance

This file contains results about Abs that require the full CStarAlgebra machinery.
-/

section CStar

/- This section should be moved to `ForMathlib/Analysis/CStarAlgebra/SpecialFunctions/Abs.lean`. -/


variable [NonUnitalNormedRing A] [StarRing A]
variable [PartialOrder A] [StarOrderedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [CStarRing A]

@[simp]
lemma abs_eq_zero_iff {a : A}  : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[simp]
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    abs_nonneg.star_eq, abs_mul_abs_self, CStarRing.norm_star_mul_self]

end CStar
