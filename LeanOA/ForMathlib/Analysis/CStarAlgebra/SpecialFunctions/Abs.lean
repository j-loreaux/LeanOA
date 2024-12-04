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

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma cfcₙ_sq {a : A} {f : ℂ → ℂ} (hf : ContinuousOn f (quasispectrum ℂ a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac):
  cfcₙ (fun z : ℂ ↦ ((f z) ^ 2 : ℂ)) a = (cfcₙ f a) * (cfcₙ f a) := by
  rw [← cfcₙ_mul ..]
  simp only [Complex.norm_eq_abs, sq]

lemma cfcₙ_sq' {a : A} {f : ℂ → ℂ} (hf : ContinuousOn f (quasispectrum ℂ a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac):
  cfcₙ (fun z : ℂ ↦ ((f z) ^ 2 : ℂ)) a = cfcₙ (fun z : ℂ ↦ ((f z) * (f z) : ℂ)) a := by
  rw [cfcₙ_sq ..]
  apply Eq.symm (cfcₙ_mul f f a hf hf0 hf hf0)

variable [PartialOrder A] [StarOrderedRing A]

lemma abs_eq_cfcₙ_norm {a : A} (ha : IsSelfAdjoint a) :
    abs a = cfcₙ (‖·‖) a := by
   simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq]
   rw [sqrt_eq_cfcₙ_real_sqrt (star_mul_self_nonneg a), ha.star_eq, sqrt_mul_self_rfl ha]

lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsSelfAdjoint.mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) : 0 ≤ a * a := by
  simpa [ha.star_eq] using star_mul_self_nonneg a

open ComplexOrder in
lemma cfcₙ_norm_sq_nonneg {f : ℂ → ℂ} {a : A} : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _

open ComplexOrder in
lemma cfcₙ_norm_nonneg {a : A} : 0 ≤ cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp only [Complex.norm_eq_abs, Complex.zero_le_real, apply_nonneg]

lemma abs_sq_eq_cfcₙ_norm_sq_complex {a : A} (ha : IsStarNormal a) :
    abs a ^ (2 : NNReal) = cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a := by
  conv_lhs => rw [abs_sq_eq_star_mul_self, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_mul ..]
  exact cfcₙ_congr fun x hx ↦ Complex.conj_mul' x

/-- Will omit this one. It can't possibly be useful. -/
lemma abs_mul_self_eq_cfcₙ_norm_mul_self {a : A} (ha : IsStarNormal a) :
    abs a * abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a * cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  rw [← cfcₙ_sq, abs_mul_self_eq_star_mul_self, ← abs_sq_eq_star_mul_self]
  exact abs_sq_eq_cfcₙ_norm_sq_complex ha

/- One should be able to use some kind of congrFun or congrArg thing. -/
lemma abs_eq_cfcₙ_norm_complex {a : A} (ha : IsStarNormal a) :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  calc
    abs a = sqrt ((abs a) ^ (2 : NNReal)) := by rw [CFC.sqrt_nnrpow_two ..]
        _ = sqrt (cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a) := by
          conv => enter [1,1]; rw [abs_sq_eq_cfcₙ_norm_sq_complex ha]
        _ = sqrt ((cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a) * (cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a)) := by rw [cfcₙ_sq ..]
        _ = (cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a) := by
          rw [← CFC.nnrpow_two (cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a) _,CFC.sqrt_nnrpow_two (cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a) _]
          <;> exact cfcₙ_norm_nonneg

lemma abs_of_nonneg {a : A} (ha : 0 ≤ a) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a = a⁺ + a⁻ := by
  rw [CFC.posPart_def, CFC.negPart_def, ← cfcₙ_add .., abs_eq_cfcₙ_norm ha]
  exact cfcₙ_congr fun x hx ↦ (posPart_add_negPart x).symm

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻ := by
  nth_rw 2 [← CFC.posPart_sub_negPart a]
  rw [CFC.posPart_add_negPart a]
  abel

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺ := by
  nth_rw 2 [← CFC.posPart_sub_negPart a]
  rw [CFC.posPart_add_negPart a]
  abel

-- `r` of the appropriate kinds, so this is actually multiple lemmas. Can we get RCLike?

lemma abs_smul_real (r : ℝ) (a : A) (ha : IsSelfAdjoint a) : abs (r • a) = |r| • abs a := by
  rw [abs_eq_cfcₙ_norm ha, ← cfcₙ_smul ..]
  conv => rhs; lhs; ext x; rw [Real.norm_eq_abs , smul_eq_mul, ← abs_mul, ← smul_eq_mul]
  rw [abs_eq_cfcₙ_norm (IsSelfAdjoint.smul (hr := by rfl) ha)]
  exact Eq.symm (cfcₙ_comp_smul r _ a (by cfc_cont_tac) (_root_.abs_zero) ha)

/- This belongs in a different file. -/
instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
  star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r) |>.smul_right r

lemma abs_smul_complex (r : ℂ) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  have : 0 ≤ ‖r‖ • abs a := smul_nonneg (by positivity) abs_nonneg
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) this]
  simp only [mul_smul_comm, smul_mul_assoc, star_smul, abs_mul_self_eq_star_mul_self]
  match_scalars
  simp only [Complex.coe_algebraMap, ← sq, mul_one, RCLike.star_def, mul_comm r, Complex.conj_mul']

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- for these you need the algebra to be unital
lemma abs_algebraMap_complex (z : ℂ) : abs (algebraMap ℂ A z) = algebraMap ℝ A |z| := sorry
lemma abs_algebraMap_real (x : ℝ) : abs (algebraMap ℝ A x) = algebraMap ℝ A |x| := sorry
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := sorry
lemma abs_natCast (n : ℕ) : abs (n : A) = n := sorry

/- Not sure if the following need Unital. -/

@[simp] lemma abs_neg (a : A) : abs (-a) = abs a := sorry
lemma abs_of_nonpos {a : A} (ha : a ≤ 0) : abs a = -a := sorry
@[simp] lemma abs_one : abs (1 : A) = 1 := sorry
@[simp] lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := sorry
lemma abs_star {a : A} (ha : IsStarNormal a) : abs (star a) = abs a := sorry

end Unital

end CFC
