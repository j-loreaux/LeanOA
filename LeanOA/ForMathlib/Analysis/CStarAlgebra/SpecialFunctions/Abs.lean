/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file provides API for the absolute value for (CFC) and (CFCₙ), and includes the associated
basic API. THIS NEEDS UPDATING!

## Main declarations

## Implementation notes

None yet

## Notation

Not sure we will need this

## TODO

Not sure yet.

-/

open scoped NNReal

namespace CFC

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

lemma mul_self_eq_mul_self {a : A} (ha : IsSelfAdjoint a) : a * a =
    cfcₙ (fun (x : ℝ) ↦ x * x) a := by
  conv_lhs => rw [← cfcₙ_id' ℝ a, ← cfcₙ_mul ..]

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

/-- Needs a new name. -/
lemma sqrt_mul_self_rfl {a : A} (ha : IsSelfAdjoint a) :
    cfcₙ Real.sqrt (a * a) = cfcₙ (fun x ↦ √(x * x)) a := by
  rw [mul_self_eq_mul_self ha, ← cfcₙ_comp a (f := fun x ↦ x * x) (g := fun x ↦ √x),
     Function.comp_def]

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A]
   [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
   [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
   [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
   [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

lemma sqrt_eq_cfcₙ_real_sqrt {a : A} (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)),
    ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma abs_eq_cfcₙ_norm {a : A} (ha : IsSelfAdjoint a) :
    abs a = cfcₙ (‖·‖) a := by
   simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq]
   rw [sqrt_eq_cfcₙ_real_sqrt (star_mul_self_nonneg a), ha.star_eq, sqrt_mul_self_rfl ha]

lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsSelfAdjoint.mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) : 0 ≤ a * a := by
  simpa [ha.star_eq] using star_mul_self_nonneg a

lemma cfcₙ_norm_sq_nonneg {a : A} (ha : IsStarNormal a) : 0 ≤ cfcₙ (fun z : ℂ ↦ (star z * z : ℂ)) a := by
  apply (nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts).mpr
  constructor
  · sorry
  · --have := spectrum_star_mul_self_nonneg
    sorry

open ComplexConjugate in
lemma abs_sq_eq_cfcₙ_norm_sq_complex (a : A) (ha : IsStarNormal a) :
    abs a ^ (2 : NNReal) = cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a := by
  rw [abs]
  conv_rhs =>
   lhs
   ext
   rw [← Complex.conj_mul']
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  refine (nnrpow_inv_eq (cfcₙ (fun x => star x * x) a) (star a * a) ?hx ?ha ?hb).mp ?_
  · exact Ne.symm (zero_ne_one' ℝ≥0)
  · exact cfcₙ_norm_sq_nonneg ha
  · exact star_mul_self_nonneg a
  · sorry --So this really doesn't do anything at all...notice that it just recasts uselessly.

#exit

/- The result above may be easier to begin with. -/
open ComplexConjugate in
lemma abs_eq_cfcₙ_norm_complex (a : A) [ha : IsStarNormal a] :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq, Complex.conj_mul', Complex.ofReal_pow _ 2]
  --abs a becomes √(star a * a).
  --We need that ‖z‖ = √(star z * z), where star z is the complex conjugate of z.
  --Somehow the square root should be real, but our theorem above might handle this.
  have H (z : ℂ) := (Complex.conj_mul' z)--note complex hPow.
  have K (z : ℂ) : Complex.im (star z * z) = 0 := by
    simp only [RCLike.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im, neg_mul]
    rw [mul_comm, add_neg_cancel]--I can't believe this isn't in the library already!
  rw [sqrt_eq_cfcₙ_real_sqrt (star_mul_self_nonneg a)]
  have L (z : ℂ) : Complex.im z = 0 ↔ z = Complex.re z := by
    constructor
    · intro h
      exact Eq.symm (Complex.ext rfl (id (Eq.symm h)))
    · intro h
      exact
        (AddSemiconjBy.eq_zero_iff (z.re : ℂ).im
            (congrFun (congrArg HAdd.hAdd (congrArg Complex.im (id (Eq.symm h)))) (z.re : ℂ).im)).mp
          rfl
  have LL (z : ℂ) := (L <| star z * z).mp <| K z
  have LLL (x : ℝ) : Complex.ofReal (x ^ 2) = (Complex.ofReal x) ^ 2 := Complex.ofReal_pow x 2
  --using this last lemma, the entire proof can probably be simplified using some real
  --squareroot lemma...

#exit

lemma abs_of_nonneg {a : A} (ha : 0 ≤ a) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

--The following results seem to amount to translating over to functions.

lemma abs_eq_posPart_add_negPart (a : A) (ha : IsSelfAdjoint a) : abs a = a⁺ + a⁻ := sorry

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻ := sorry

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺ := sorry

-- `r` of the appropriate kinds, so this is actually multiple lemmas
lemma abs_smul : abs (r • a) = |r| • abs a := sorry

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- for these you need the algebra to be unital
lemma abs_algebraMap_complex (z : ℂ) : abs (algebraMap ℂ A z) = algebraMap ℝ A |z| := sorry
lemma abs_algebraMap_real (x : ℝ) : abs (algebraMap ℝ A x) = algebraMap ℝ A |x| := sorry
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := sorry
lemma abs_natCast (n : ℕ) : abs (n : A) = n := sorry

end Unital

end CFC
