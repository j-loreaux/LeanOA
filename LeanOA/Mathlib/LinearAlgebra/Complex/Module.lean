import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Complex.Module

open scoped ComplexStarModule

namespace ComplexStarModule

variable {M : Type*} [AddCommGroup M] [StarAddMonoid M] [Module ℂ M] [StarModule ℂ M] {x y : M}

lemma ext (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x, ← realPart_add_I_smul_imaginaryPart y, h₁, h₂]

lemma ext_iff : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y := ⟨by grind, fun h ↦ ext h.1 h.2⟩

end ComplexStarModule

@[simp]
theorem ker_imaginaryPart {E : Type*} [AddCommGroup E]
    [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E] :
    imaginaryPart.ker = selfAdjoint.submodule ℝ E := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]
lemma imaginaryPart_eq_zero_iff {A : Type*} [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] {x : A} :
    ℑ x = 0 ↔ IsSelfAdjoint x := by
  simpa [-ker_imaginaryPart] using SetLike.ext_iff.mp ker_imaginaryPart x

@[simp]
lemma realPart_one {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] :
    ℜ (1 : A) = 1 := by
  ext; simp [realPart_apply_coe, ← two_smul ℝ]

open Complex in
/-- An element in a non-unital star `ℂ`-algebra is normal if and only if its real and imaginary
parts commute. -/
lemma isStarNormal_iff_commute_realPart_imaginaryPart
    {A : Type*} [NonUnitalNonAssocRing A] [StarRing A]
    [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    {x : A} : IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A) := by
  conv_lhs => rw [isStarNormal_iff, ← realPart_add_I_smul_imaginaryPart x]
  rw [commute_iff_eq]
  simp only [star_add, selfAdjoint.star_val_eq, star_smul, Complex.star_def, Complex.conj_I,
    neg_smul, ← sub_eq_add_neg, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub,
    smul_smul, Complex.I_mul_I, one_smul, sub_neg_eq_add, mul_sub, add_mul, smul_add]
  rw [sub_eq_add_neg, add_assoc, add_sub_assoc, add_left_cancel_iff, ← sub_add,
    ← add_assoc, add_right_cancel_iff, ← sub_eq_zero, sub_sub_eq_add_sub, add_assoc, ← two_nsmul,
    add_comm, sub_eq_add_neg, add_assoc, ← two_nsmul, smul_neg, ← sub_eq_add_neg, sub_eq_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ congr(2 • I • $h)⟩
  have := congr(I • (2⁻¹ : ℂ) • $h)
  rw [← smul_one_smul ℂ 2 (I • (ℑ x * ℜ x : A)), ← smul_one_smul ℂ 2] at this
  simpa

lemma star_mul_self_eq_add_I_smul {A : Type*} [NonUnitalNonAssocRing A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    (x : A) : star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
  simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  grind

lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq {A : Type*} [NonUnitalNonAssocRing A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    {x : A} [hx : IsStarNormal x] : star x * x = ℜ x * ℜ x + ℑ x * ℑ x := by
  simp [star_mul_self_eq_add_I_smul, isStarNormal_iff_commute_realPart_imaginaryPart.mp hx |>.eq]

lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one {A : Type*} [Ring A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A] {x : A} :
    x ∈ unitary A ↔ IsStarNormal x ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A) := by
  rw [Unitary.mem_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hx, h⟩ ↦ ?_⟩
  · have : IsStarNormal x := by simp [isStarNormal_iff, commute_iff_eq, h]
    rw [star_mul_self_eq_realPart_sq_add_imaginaryPart_sq] at h
    exact ⟨this, by simp [sq, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq, h]
