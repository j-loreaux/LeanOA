/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file provides basic API for `CFC.abs` for `CStarAlgebra`s.

# TODO

There is likely an `RCLike` version of `abs_smul_complex`.


-/

open scoped NNReal

namespace CFC

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A]

section IsSelfAdjoint

variable [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

lemma mul_self_eq_mul_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : a * a =
    cfcₙ (fun (x : ℝ) ↦ x * x) a := by
  conv_lhs => rw [← cfcₙ_id' ℝ a, ← cfcₙ_mul ..]
section Unique

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma cfcₙ_sqrt_mul_self {a : A} (ha : IsSelfAdjoint a) :
    cfcₙ Real.sqrt (a * a) = cfcₙ (fun x ↦ √(x * x)) a := by
  rw [mul_self_eq_mul_self ha, ← cfcₙ_comp a (f := fun x ↦ x * x) (g := fun x ↦ √x),
     Function.comp_def]

section NonnegSpectrumClass

variable [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

lemma sqrt_eq_real_sqrt {a : A} (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)),
    ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

lemma abs_of_nonneg {a : A} (ha : 0 ≤ a) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

lemma abs_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    abs a = cfcₙ (‖·‖) a := by
   simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq]
   rw [sqrt_eq_real_sqrt (star_mul_self_nonneg a), ha.star_eq, cfcₙ_sqrt_mul_self ha]

section CStarRing

variable [CStarRing A]

lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

end CStarRing

end NonnegSpectrumClass

end Unique

end IsSelfAdjoint

section ComplexCFC

variable [PartialOrder A] [StarOrderedRing A]
variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

open ComplexOrder in
lemma cfcₙ_norm_sq_nonneg {f : ℂ → ℂ} {a : A} : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _

open ComplexOrder in
lemma cfcₙ_norm_nonneg {a : A} : 0 ≤ cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp only [Complex.norm_eq_abs, Complex.zero_le_real, apply_nonneg]

section Nonneg

variable [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

lemma abs_sq_eq_cfcₙ_norm_sq_complex {a : A} (ha : IsStarNormal a) :
    abs a ^ (2 : NNReal) = cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a := by
  conv_lhs => rw [abs_nnrpow_two, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_mul ..]
  exact cfcₙ_congr fun x hx ↦ Complex.conj_mul' x

section NonnegSpectrumClass

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℂ A]
variable [NonnegSpectrumClass ℝ A]

lemma abs_eq_cfcₙ_norm_complex {a : A} (ha : IsStarNormal a) :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  conv_lhs => rw [abs, ← abs_nnrpow_two, sqrt_eq_real_sqrt, cfcₙ_real_eq_complex,
    abs_sq_eq_cfcₙ_norm_sq_complex ha, ← cfcₙ_comp' ..]
  exact cfcₙ_congr fun x hx ↦ by simp [sq]

end NonnegSpectrumClass

end Nonneg

end ComplexCFC

section RealAlgebra

variable [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NonnegSpectrumClass ℝ A]

protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a = a⁺ + a⁻ := by
  rw [CFC.posPart_def, CFC.negPart_def, ← cfcₙ_add .., abs_eq_norm ha]
  exact cfcₙ_congr fun x hx ↦ (posPart_add_negPart x).symm

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻ := by
  nth_rw 2 [← CFC.posPart_sub_negPart a]
  rw [CFC.posPart_add_negPart a]
  abel

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺ := by
  nth_rw 2 [← CFC.posPart_sub_negPart a]
  rw [CFC.posPart_add_negPart a]
  abel

end RealAlgebra

section AbsSMul

variable [PartialOrder A] [StarOrderedRing A]
variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
variable [OrderedSMul ℝ A] [StarModule ℂ A]

instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
  star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r) |>.smul_right r

lemma abs_smul_complex (r : ℂ) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  have : 0 ≤ ‖r‖ • abs a := smul_nonneg (by positivity) abs_nonneg
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) this]
  simp only [mul_smul_comm, smul_mul_assoc, abs_mul_self, star_smul]
  match_scalars
  rw [mul_one, mul_one, ← sq, mul_comm, RCLike.star_def, Complex.conj_mul', Complex.norm_eq_abs, ← Complex.coe_algebraMap]

lemma abs_smul_real (r : ℝ) (a : A) : abs (r • a) = |r| • abs a := by
  simpa only [Complex.coe_smul, Complex.norm_real, Real.norm_eq_abs] using abs_smul_complex (Complex.ofReal r) _

end AbsSMul
section NonUnital







#exit


--variable [NonUnitalCStarAlgebra A]

/- This belongs in a different file when brought to Mathlib. -/
instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
  star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r) |>.smul_right r

lemma abs_smul_complex (r : ℂ) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  have : 0 ≤ ‖r‖ • abs a := smul_nonneg (by positivity) abs_nonneg
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) this]
  simp only [mul_smul_comm, smul_mul_assoc, star_smul, abs_mul_self]
  match_scalars
  simp only [Complex.coe_algebraMap, ← sq, mul_one, RCLike.star_def, mul_comm r, Complex.conj_mul']

lemma abs_smul_real (r : ℝ) (a : A) : abs (r • a) = |r| • abs a := by
  simpa only [Complex.coe_smul, Complex.norm_real, Real.norm_eq_abs] using abs_smul_complex (Complex.ofReal r) _

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp]
lemma abs_one : abs (1 : A) = 1 := by
  rw [abs, star_one , mul_one, sqrt_one]

@[simp]
lemma abs_neg (a : A) : abs (-a) = abs a := by
  rw [← neg_one_smul ℝ a, abs_smul_real, _root_.abs_neg, _root_.abs_one, one_smul]

lemma abs_of_nonpos {a : A} (ha : a ≤ 0) : abs a = -a := by
  simp only [← abs_neg a, abs_of_nonneg <| neg_nonneg.mpr ha]

@[simp]
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    abs_nonneg.star_eq, abs_mul_self, CStarRing.norm_star_mul_self]

lemma abs_star {a : A} (ha : IsStarNormal a) : abs (star a) = abs a := by
  rw [abs, abs, star_comm_self, star_star]

lemma abs_algebraMap_complex (c : ℂ) : abs (algebraMap ℂ A c) = algebraMap ℝ A (Complex.abs c : ℝ) := by
  simp only [Algebra.algebraMap_eq_smul_one, abs_smul_complex, Complex.norm_eq_abs, abs_one]

lemma abs_algebraMap_real (c : ℝ) : abs (algebraMap ℝ A c) = algebraMap ℝ A |c| := by
  simpa only [Complex.abs_ofReal] using abs_algebraMap_complex (Complex.ofReal _)

lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := by
  simpa only [NNReal.abs_eq] using abs_algebraMap_real (NNReal.toReal _)

lemma abs_natCast (n : ℕ) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_real (n : ℝ)

end Unital

end CFC
