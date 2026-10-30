module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic

public section

variable {R : Type*}

variable (R) in
/-- A *proper star* is when `star x * x = 0` implies `x = 0`. -/
class IsProperStar [Mul R] [Zero R] [Star R] : Prop where
  eq_zero_of_star_mul_self_eq_zero {x : R} : star x * x = 0 → x = 0

@[simp] lemma star_mul_self_eq_zero [MulZeroClass R] [Star R] [IsProperStar R] {x : R} :
    star x * x = 0 ↔ x = 0 :=
  ⟨IsProperStar.eq_zero_of_star_mul_self_eq_zero, fun h ↦ by simp [h]⟩

lemma star_mul_self_ne_zero [MulZeroClass R] [Star R] [IsProperStar R] {x : R} :
    star x * x ≠ 0 ↔ x ≠ 0 := by simp

@[simp] lemma mul_star_self_eq_zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R]
    [IsProperStar R] {x : R} : x * star x = 0 ↔ x = 0 := by
  simpa using star_mul_self_eq_zero (x := star x)

lemma mul_star_self_ne_zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R]
    [IsProperStar R] {x : R} : x * star x ≠ 0 ↔ x ≠ 0 := by simp

instance (priority := low) [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] [StarRing R] :
    IsProperStar R where eq_zero_of_star_mul_self_eq_zero := by simp

instance {S : Type*} [MulZeroClass R] [Star R] [IsProperStar R]
    [MulZeroClass S] [Star S] [IsProperStar S] : IsProperStar (R × S) where
  eq_zero_of_star_mul_self_eq_zero := by simp [Prod.ext_iff]

instance {ι : Type*} {S : ι → Type*} [Π i, MulZeroClass (S i)] [Π i, Star (S i)]
    [∀ i, IsProperStar (S i)] : IsProperStar (Π i, S i) where
  eq_zero_of_star_mul_self_eq_zero := by simp [funext_iff]

instance [NonUnitalNonAssocSemiring R] [StarAddMonoid R] [IsProperStar R] : IsProperStar Rᵐᵒᵖ where
  eq_zero_of_star_mul_self_eq_zero := by simp [← MulOpposite.op_star, ← MulOpposite.op_mul]


@[simp] theorem star_mul_self_pos_iff [NonUnitalSemiring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [IsProperStar R] {x : R} :
    0 < star x * x ↔ x ≠ 0 := by
  simp [lt_iff_le_and_ne']

@[simp] theorem mul_star_self_pos_iff [NonUnitalSemiring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [IsProperStar R] {x : R} : 0 < x * star x ↔ x ≠ 0 := by
  simp [lt_iff_le_and_ne']

instance [NonUnitalNormedRing R] [StarRing R] [CStarRing R] : IsProperStar R where
  eq_zero_of_star_mul_self_eq_zero {x} := by
    rw [← norm_eq_zero, CStarRing.norm_star_mul_self]; simp
