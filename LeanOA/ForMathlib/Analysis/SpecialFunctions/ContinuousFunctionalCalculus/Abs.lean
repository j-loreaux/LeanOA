/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file defines the absolute value via the (unital and non unital) continuous functional calculus
(CFC) and (CFCₙ), and includes foundational API.

## Main declarations

+ `CFC.abs`: The absolute value declaration as `abs a := sqrt (star a) * a`.

# TODO

There is likely an `RCLike` version of `abs_smul_complex`.

-/

open scoped NNReal

namespace CFC

section Generic

variable {A : Type*}

section NonUnital

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
variable [PartialOrder A] [StarOrderedRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A]

/-- The absolute value of an operator, using the nonunital continuous functional calculus. -/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp]
lemma abs_neg (a : A) : abs (-a) = abs a := by
  simp [abs]

@[simp]
lemma abs_nonneg {a : A} : 0 ≤ abs a := sqrt_nonneg

lemma abs_star {a : A} (ha : IsStarNormal a) : abs (star a) = abs a := by
  simp [abs, star_comm_self]

@[simp]
lemma abs_zero : abs (0 : A) = 0 := by
  rw [abs, star_zero, mul_zero, sqrt_zero]

variable [IsTopologicalRing A] [T2Space A]

lemma abs_mul_self (a : A) : abs a * abs a = star a * a := by
  refine sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

lemma abs_nnrpow_two (a : A) : abs a ^ (2 : ℝ≥0) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_self

lemma abs_nnrpow_two_mul (a : A) (x : ℝ≥0) :
    (abs a) ^ (2 * x) = (star a * a) ^ x := by rw [← nnrpow_nnrpow, abs_nnrpow_two]

lemma abs_nnrpow (a : A) (x : ℝ≥0) :
    (abs a) ^ x = (star a * a) ^ (x / 2) := by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

lemma sqrt_eq_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)),
    ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

lemma abs_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

lemma abs_of_nonpos {a : A} (ha : a ≤ 0) : abs a = -a := by
  simp only [← abs_neg a, abs_of_nonneg <| neg_nonneg.mpr ha]

lemma abs_eq_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfcₙ (‖·‖) a := by
   simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq]
   have H : cfcₙ Real.sqrt (a * a) = cfcₙ (fun x ↦ √(x * x)) a := by
       rw [← Function.comp_def, cfcₙ_comp a (f := fun x ↦ x * x) (g := fun x ↦ √x), cfcₙ_mul .., cfcₙ_id' ..]
   rw [sqrt_eq_real_sqrt (star_mul_self_nonneg a), ha.star_eq, H]

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

@[simp]
lemma abs_abs (a : A) : abs (abs a) = abs a :=
  abs_of_nonneg abs_nonneg

variable [StarModule ℝ A]

lemma abs_smul_real (r : ℝ) (a : A) : abs (r • a) = |r| • abs a := by
  have : 0 ≤ |r| • abs a := smul_nonneg (by positivity) abs_nonneg
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) this]
  simp only [mul_smul_comm, smul_mul_assoc, abs_mul_self, star_smul]
  match_scalars
  simp

lemma abs_smul_nnreal (r : ℝ≥0) (a : A) : abs (r • a) = r • abs a := by
  simpa [NNReal.abs_eq] using abs_smul_real r a

end Real

section Complex

variable [NonUnitalRing A] [TopologicalSpace A] [Module ℂ A]

variable [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

open ComplexOrder in
lemma cfcₙ_norm_sq_nonneg {f : ℂ → ℂ} {a : A} : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _

open ComplexOrder in
lemma cfcₙ_norm_nonneg {a : A} : 0 ≤ cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp only [Complex.zero_le_real, norm_nonneg]

variable [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]

lemma abs_sq_eq_cfcₙ_norm_sq_complex {a : A} (ha : IsStarNormal a) :
    abs a ^ (2 : NNReal) = cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a := by
  conv_lhs => rw [abs_nnrpow_two, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_mul ..]
  exact cfcₙ_congr fun x hx ↦ Complex.conj_mul' x

lemma abs_eq_cfcₙ_norm_complex {a : A} (ha : IsStarNormal a) :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  conv_lhs => rw [abs, ← abs_nnrpow_two, sqrt_eq_real_sqrt, cfcₙ_real_eq_complex,
    abs_sq_eq_cfcₙ_norm_sq_complex ha, ← cfcₙ_comp' ..]
  exact cfcₙ_congr fun x hx ↦ by simp [sq]

lemma cfcₙ_abs_complex (f : ℂ → ℂ) (a : A) (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℂ)) '' quasispectrum ℂ a) := by cfc_cont_tac) :
    cfcₙ f (abs a) = cfcₙ (fun x ↦ f ‖x‖) a := by
  rw [abs_eq_cfcₙ_norm_complex ha]
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [← cfcₙ_comp' ..]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0, cfcₙ_apply_of_not_map_zero _ (fun h ↦ (hf0 <| by simpa using h).elim)]

variable [StarModule ℂ A] in
lemma abs_smul_complex (r : ℂ) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  have : 0 ≤ ‖r‖ • abs a := smul_nonneg (by positivity) abs_nonneg
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _) this]
  simp only [mul_smul_comm, smul_mul_assoc, abs_mul_self, star_smul]
  match_scalars
  rw [mul_one, mul_one, ← sq, mul_comm, RCLike.star_def, Complex.conj_mul', ← Complex.coe_algebraMap]

end Complex

end NonUnital

section Unital

section Real

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
variable [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A]

@[simp]
lemma abs_one : abs (1 : A) = 1 := by
  rw [abs, star_one , mul_one, sqrt_one]

variable [StarModule ℝ A]

lemma abs_algebraMap_real (c : ℝ) : abs (algebraMap ℝ A c) = algebraMap ℝ A |c| := by
  simp only [Algebra.algebraMap_eq_smul_one, abs_smul_real, abs_one]

lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := by
  simpa only [NNReal.abs_eq] using abs_algebraMap_real (NNReal.toReal _)

lemma abs_natCast (n : ℕ) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_real (n : ℝ)

end Real

section Complex

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℂ A] [IsTopologicalRing A] [T2Space A]
variable [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [StarModule ℂ A]

lemma abs_algebraMap_complex (c : ℂ) : abs (algebraMap ℂ A c) = algebraMap ℝ A (norm c : ℝ) := by
  simp only [Algebra.algebraMap_eq_smul_one, abs_smul_complex, abs_one]

end Complex

end Unital

end Generic

section CStar

variable [NonUnitalNormedRing A] [StarRing A]
variable [PartialOrder A] [StarOrderedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [CStarRing A]

lemma abs_eq_zero_iff {a : A}  : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[simp]
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    abs_nonneg.star_eq, abs_mul_self, CStarRing.norm_star_mul_self]

end CStar

end CFC
