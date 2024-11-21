import Mathlib
import LeanOA.CFCRange

/-! # Product of commuting nonnegative elements is nonnnegative -/

open scoped NNReal

namespace CFC

-- it seems like some of the hypotheses are wrong near `CFC.sqrt`.
variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A]
    [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

lemma sqrt_eq_cfcₙ_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)), ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

end CFC

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace CStarAlgebra

-- this lemma is totally generic for the cfc and should be include in the base file.
-- do we want it for convenience? the unital version has `cfc_pow_id`.
lemma mul_self_eq_cfcₙ_mul_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : a * a = cfcₙ (fun (x : ℝ) ↦ x * x) a := by
  conv_lhs => rw [← cfcₙ_id' ℝ a, ← cfcₙ_mul ..]

variable [PartialOrder A] [StarOrderedRing A]

lemma Commute.mul_nonneg {a b : A} (hab : Commute a b)
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    0 ≤ a * b := by
  rw [← CFC.sqrt_mul_sqrt_self a, CFC.sqrt_eq_cfcₙ_real_sqrt a, mul_assoc,
    (ha.isSelfAdjoint.commute_cfcₙ hab Real.sqrt).eq, ← mul_assoc, ← CFC.sqrt_eq_cfcₙ_real_sqrt a]
  exact conjugate_nonneg_of_nonneg hb CFC.sqrt_nonneg

end CStarAlgebra
