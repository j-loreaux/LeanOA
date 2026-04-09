import Mathlib.Analysis.CStarAlgebra.Classes

/-- A multiplicative magma is **unital** if there exists a unit.

**Note**: Do not use this unless it is the only reasonable way to phrase or prove a statement.
In general you should use `NonUnitalRing`, `Ring`, etc. -/
@[mk_iff] class IsUnital (A : Type*) [Mul A] : Prop where
  isUnital : ∃ u : A, ∀ x : A, u * x = x ∧ x * u = x

/-- A multiplicative magma is **not-unital** if there does not exist a unit. -/
@[mk_iff] class IsNotUnital (A : Type*) [Mul A] : Prop where
  isNotUnital : ∀ u : A, ∃ x : A, u * x ≠ x ∨ x * u ≠ x

@[simp] lemma not_isUnital_iff_isNotUnital {A : Type*} [Mul A] : ¬IsUnital A ↔ IsNotUnital A := by
  simp [isUnital_iff, isNotUnital_iff, -not_and, not_and_or]

@[simp] lemma not_isNotUnital_iff_isUnital {A : Type*} [Mul A] : ¬IsNotUnital A ↔ IsUnital A := by
  grind [not_isUnital_iff_isNotUnital]

variable (A : Type*)

/-- A unital magma is `MulOneClass`. -/
noncomputable abbrev IsUnital.toMulOneClass [Mul A] [h : IsUnital A] :
    MulOneClass A where
  one := h.isUnital.choose
  one_mul a := (h.isUnital.choose_spec a).1
  mul_one a := (h.isUnital.choose_spec a).2

lemma MulOneClass.isUnital [MulOneClass A] : IsUnital A where
  isUnital := ⟨1, fun x ↦ ⟨one_mul x, mul_one x⟩⟩

noncomputable section
namespace IsUnital

attribute [local instance] IsUnital.toMulOneClass

/-- A unital semigroup is a monoid. -/
abbrev toMonoid [Semigroup A] [h : IsUnital A] : Monoid A where

/-- A unital non-associative semiring is a non-associative semiring. -/
abbrev toNonAssocSemiring [NonUnitalNonAssocSemiring A] [IsUnital A] : NonAssocSemiring A where

/-- A unital non-unital non-associative commutative semiring is a non-associative
commutative semiring. -/
abbrev toNonAssocCommSemiring [NonUnitalNonAssocCommSemiring A] [IsUnital A] :
    NonAssocCommSemiring A where

/-- A unital non-unital semiring is a semiring. -/
abbrev toSemiring [NonUnitalSemiring A] [IsUnital A] : Semiring A where

/-- A unital non-unital commutative semiring is a commutative semiring. -/
abbrev toCommSemiring [NonUnitalCommSemiring A] [IsUnital A] : CommSemiring A where

/-- A unital non-unital non-associative ring is a non-associative ring. -/
abbrev toNonAssocRing [NonUnitalNonAssocRing A] [IsUnital A] : NonAssocRing A where

/-- A unital non-unital non-associative commutative ring is a non-associative commutative ring. -/
abbrev toNonAssocCommRing [NonUnitalNonAssocCommRing A] [IsUnital A] : NonAssocCommRing A where

/-- A unital non-unital ring is a ring. -/
abbrev toRing [NonUnitalRing A] [IsUnital A] : Ring A where

/-- A unital non-unital commutative ring is a commutative ring. -/
abbrev toCommRing [NonUnitalCommRing A] [IsUnital A] : CommRing A where

attribute [local instance] IsUnital.toSemiring in
/-- A unital non-unital algebra is an algebra. -/
abbrev toAlgebra {R} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [IsUnital A] : Algebra R A := .ofModule smul_mul_assoc mul_smul_comm

/-- A unital non-unital C⋆-algebra is a C⋆-algebra. -/
abbrev toCStarAlgebra [NonUnitalCStarAlgebra A] [h : IsUnital A] : CStarAlgebra A where
  __ := ‹NonUnitalCStarAlgebra A›
  __ := h.toSemiring
  __ := h.toAlgebra

attribute [local instance] IsUnital.toCStarAlgebra in
/-- A unital non-unital commutative C⋆-algebra is a commutative C⋆-algebra. -/
abbrev toCommCStarAlgebra [NonUnitalCommCStarAlgebra A] [h : IsUnital A] : CommCStarAlgebra A where

end IsUnital
end
