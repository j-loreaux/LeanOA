import Mathlib.Analysis.CStarAlgebra.Classes

/-- A multiplicative magma is **unital** if there exists a unit. -/
class IsUnital (A : Type*) [Mul A] : Prop where
  isUnital : ∃ u : A, ∀ x : A, u * x = x ∧ x * u = x

variable (A : Type*)

/-- A unital magma is `MulOneClass`. -/
noncomputable abbrev IsUnital.toMulOneClass {A : Type*} [Mul A] [h : IsUnital A] :
    MulOneClass A where
  one := h.isUnital.choose
  one_mul a := (h.isUnital.choose_spec a).1
  mul_one a := (h.isUnital.choose_spec a).2

/-- A `MulOneClass` is unital. -/
abbrev MulOneClass.isUnital [MulOneClass A] : IsUnital A where
  isUnital := ⟨1, fun x ↦ ⟨one_mul x, mul_one x⟩⟩

attribute [local instance] IsUnital.toMulOneClass

/-- A unital semigroup is a monoid. -/
noncomputable abbrev IsUnital.toMonoid [Semigroup A] [h : IsUnital A] : Monoid A where

/-- A unital non-associative semiring is a non-associative semiring. -/
noncomputable abbrev IsUnital.toNonAssocSemiring [NonUnitalNonAssocSemiring A] [IsUnital A] :
    NonAssocSemiring A where

/-- A unital non-unital semiring is a semiring. -/
noncomputable abbrev IsUnital.toSemiring [NonUnitalSemiring A] [IsUnital A] : Semiring A where

/-- A unital non-unital commutative semiring is a commutative semiring. -/
noncomputable abbrev IsUnital.toCommSemiring [NonUnitalCommSemiring A] [IsUnital A] :
    CommSemiring A where

/-- A unital non-unital ring is a ring. -/
noncomputable abbrev IsUnital.toNonUnitalRing [NonUnitalRing A] [IsUnital A] : Ring A where

attribute [local instance] IsUnital.toSemiring in
/-- A unital non-unital algebra is an algebra. -/
noncomputable abbrev IsUnital.toAlgebra {R} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [IsUnital A] : Algebra R A :=
  .ofModule smul_mul_assoc mul_smul_comm

/-- A unital non-unital C⋆-algebra is a C⋆-algebra. -/
noncomputable abbrev IsUnital.toCStarAlgebra [NonUnitalCStarAlgebra A] [h : IsUnital A] :
    CStarAlgebra A where
  __ := ‹NonUnitalCStarAlgebra A›
  __ := h.toSemiring
  __ := h.toAlgebra
