/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file defines the absolute value via the non-unital continuous functional calculus
and includes foundational API.

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

lemma abs_star (a : A) (ha : IsStarNormal a := by cfc_tac) : abs (star a) = abs a := by
  simp [abs, star_comm_self']

@[simp]
lemma abs_zero : abs (0 : A) = 0 := by
  simp [abs]

variable [IsTopologicalRing A] [T2Space A]

lemma abs_mul_abs_self (a : A) : abs a * abs a = star a * a :=
  sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

lemma abs_nnrpow_two (a : A) : abs a ^ (2 : ℝ≥0) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs_self

lemma abs_nnrpow_two_mul (a : A) (x : ℝ≥0) :
    abs a ^ (2 * x) = (star a * a) ^ x := by rw [← nnrpow_nnrpow, abs_nnrpow_two]

lemma abs_nnrpow (a : A) (x : ℝ≥0) :
    abs a ^ x = (star a * a) ^ (x / 2) := by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

lemma sqrt_eq_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  suffices cfcₙ (fun x : ℝ ↦ √x * √x) a = cfcₙ (fun x : ℝ ↦ x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ ↦ Real.sqrt_nonneg x))] at this
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

lemma abs_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

lemma abs_of_nonpos (a : A) (ha : a ≤ 0 := by cfc_tac) : abs a = -a := by
  simpa using abs_of_nonneg (-a)

lemma abs_eq_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfcₙ (‖·‖) a := by
  conv_lhs => rw [abs, ha.star_eq, sqrt_eq_real_sqrt .., ← cfcₙ_id' ℝ a, ← cfcₙ_mul .., ← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]

protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a = a⁺ + a⁻ := by
  rw [CFC.posPart_def, CFC.negPart_def, ← cfcₙ_add .., abs_eq_norm a ha]
  exact cfcₙ_congr fun x hx ↦ (posPart_add_negPart x).symm

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a - a = 2 • a⁻ := by
  nth_rw 2 [← CFC.posPart_sub_negPart a]
  rw [CFC.posPart_add_negPart a]
  abel

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a + a = 2 • a⁺ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $((CFC.posPart_sub_negPart a).symm))

@[simp]
lemma abs_abs (a : A) : abs (abs a) = abs a :=
  abs_of_nonneg ..

variable [StarModule ℝ A]

/- Have to PR the following two lemmas to Mathlib. (I think Jireh did this already...)-/

@[elab_as_elim]
lemma Real.nnreal_dichotomy {p : ℝ → Prop} (nonneg : ∀ x : ℝ≥0, p x)
    (nonpos : ∀ x : ℝ≥0, p x → p (-x)) (r : ℝ) : p r := by
  obtain (hr | hr) : 0 ≤ r ∨ 0 ≤ -r := by simpa using le_total ..
  all_goals
    rw [← neg_neg r]
    lift (_ : ℝ) to ℝ≥0 using hr with r
    aesop

@[elab_as_elim]
lemma Real.nnreal_trichotomy {p : ℝ → Prop} (zero : p 0) (pos : ∀ x : ℝ≥0, 0 < x → p x)
    (neg : ∀ x : ℝ≥0, 0 < x → p x → p (-x)) (r : ℝ) : p r := by
  obtain (hr | rfl | hr) : 0 < r ∨ 0 = r ∨ 0 < -r := by simpa using lt_trichotomy 0 r
  case inr.inl => exact zero
  all_goals
    rw [← neg_neg r]
    lift (_ : ℝ) to ℝ≥0 using hr.le with r
    aesop


@[simp]
lemma abs_smul_nonneg {R : Type*} [LinearOrderedSemiring R] [SMulWithZero R ℝ≥0] [OrderedSMul R ℝ≥0]
    [SMul R A] [IsScalarTower R ℝ≥0 A] (r : R) (a : A) : abs (r • a) = r • abs a := by
  suffices ∀ r : ℝ≥0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs, sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) abs_nonneg)]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs_self]

@[simp]
lemma abs_smul (r : ℝ) (a : A) : abs (r • a) = |r| • abs a := by
  cases r using Real.nnreal_dichotomy
  all_goals simp [← NNReal.smul_def]

end Real

section RCLike

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜]
variable [NonUnitalRing A] [TopologicalSpace A] [Module 𝕜 A]
variable [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [NonUnitalContinuousFunctionalCalculus 𝕜 p]

open ComplexOrder

lemma cfcₙ_norm_sq_nonneg {f : 𝕜 → 𝕜} {a : A} : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _

lemma cfcₙ_norm_nonneg (f : 𝕜 → 𝕜) (a : A) : 0 ≤ cfcₙ (fun z : 𝕜 ↦ (‖f z‖ : 𝕜)) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp

variable [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

variable [StarModule 𝕜 A] [StarModule ℝ A] [IsScalarTower ℝ 𝕜 A] in
lemma abs_rclike_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  trans abs (‖r‖ • a)
  · simp [abs, mul_smul_comm, smul_mul_assoc, abs_mul_abs_self, star_smul, ← smul_assoc]
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, smul_smul, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · simp [abs_smul]

lemma abs_sq_eq_cfcₙ_norm_sq (a : A) (ha : p a := by cfc_tac) :
    abs a ^ (2 : ℝ≥0) = cfcₙ (fun z : 𝕜 ↦ (‖z‖ ^ 2 : 𝕜)) a := by
  conv_lhs => rw [abs_nnrpow_two, ← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul]

lemma abs_eq_cfcₙ_norm (a : A) (ha : p a := by cfc_tac) :
    abs a = cfcₙ (fun z : 𝕜 ↦ (‖z‖ : 𝕜)) a := by
  rw [abs, sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _), ← abs_nnrpow_two, abs_sq_eq_cfcₙ_norm_sq (𝕜 := 𝕜) a ha]
  conv_lhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_mul ..]
  simp [sq, cfcₙ_id' 𝕜 a]

lemma cfcₙ_comp_norm (f : 𝕜 → 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a) := by cfc_cont_tac) :
    cfcₙ f (abs a) = cfcₙ (fun x ↦ f ‖x‖) a := by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (fun x ↦ (‖x‖ : 𝕜)) a, ← abs_eq_cfcₙ_norm a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0, cfcₙ_apply_of_not_map_zero _ (fun h ↦ (hf0 <| by simpa using h).elim)]

end RCLike

section Complex

variable [NonUnitalRing A] [TopologicalSpace A] [Module ℂ A]

variable [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]

lemma abs_sq_eq_cfcₙ_norm_sq_complex (a : A) (ha : IsStarNormal a) :
    abs a ^ (2 : NNReal) = cfcₙ (fun z : ℂ ↦ (‖z‖ ^ 2 : ℂ)) a := by
  conv_lhs => rw [abs_nnrpow_two, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [Complex.conj_mul']

lemma abs_eq_cfcₙ_norm_complex (a : A) (ha : IsStarNormal a) :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a := by
  conv_lhs => rw [abs, ← abs_nnrpow_two, sqrt_eq_real_sqrt .., cfcₙ_real_eq_complex,
    abs_sq_eq_cfcₙ_norm_sq_complex a ha, ← cfcₙ_comp' ..]
  simp [sq]


lemma cfcₙ_abs_complex (f : ℂ → ℂ) (a : A) (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : ℂ)) '' quasispectrum ℂ a) := by cfc_cont_tac) :
    cfcₙ f (abs a) = cfcₙ (fun x ↦ f ‖x‖) a := by
  rw [abs_eq_cfcₙ_norm_complex a ha]
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [← cfcₙ_comp' ..]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0, cfcₙ_apply_of_not_map_zero _ (fun h ↦ (hf0 <| by simpa using h).elim)]

/- The following likely generalizes to `RCLike 𝕜`. -/
variable [StarModule ℂ A] in
lemma abs_complex_smul (r : ℂ) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  trans abs (‖r‖ • a)
  · simp [abs, mul_smul_comm, smul_mul_assoc, abs_mul_abs_self, star_smul, ← smul_assoc,
      ← Complex.coe_smul, Complex.mul_conj', sq]
  · simp

end Complex

end NonUnital

section Unital

section Real

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
variable [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A]

@[simp]
lemma abs_one : abs (1 : A) = 1 := by
  simp [abs]

variable [StarModule ℝ A]

lemma abs_algebraMap_real (c : ℝ) : abs (algebraMap ℝ A c) = algebraMap ℝ A |c| := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
lemma abs_natCast (n : ℕ) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_real (n : ℝ)

@[simp]
lemma abs_ofNat (n : ℕ) [n.AtLeastTwo] : abs (ofNat(n) : A) = ofNat(n) := by
  simpa using abs_natCast n

@[simp]
lemma abs_intCast (n : ℤ) : abs (n : A) = |n| := by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc, abs_neg, abs_natCast, ← Int.cast_natCast]
    congr

end Real

section Complex

variable [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℂ A] [IsTopologicalRing A] [T2Space A]
variable [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [StarModule ℂ A]

lemma abs_algebraMap_complex (c : ℂ) : abs (algebraMap ℂ A c) = algebraMap ℝ A (norm c : ℝ) := by
  simp only [Algebra.algebraMap_eq_smul_one, abs_complex_smul, abs_one]

end Complex

end Unital

end Generic

section CStar

/- This section should be moved to `ForMathlib/Analysis/CStarAlgebra/SpecialFunctions/Abs.lean`. -/


variable [NonUnitalNormedRing A] [StarRing A]
variable [PartialOrder A] [StarOrderedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [CStarRing A]

@[simp]
lemma abs_eq_zero_iff {a : A}  : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

/- Move to another file. -/
@[simp]
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    abs_nonneg.star_eq, abs_mul_abs_self, CStarRing.norm_star_mul_self]

end CStar

end CFC
