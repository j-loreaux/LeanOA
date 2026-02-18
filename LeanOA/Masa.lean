import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocCommRing A] [Module R A] [Star A]
variable (hRA : NonUnitalStarSubalgebra R A)

class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm (a b : B)  : a * b = b * a
  maximal :
    ∀ C : NonUnitalStarSubalgebra R A,
      B ≤ C → ∀ (a b : C), a * b = b * a → C ≤ B

/- Let's prove that any commutative `NonUnitalStarSubalgebra` of `A` is contained
in a Masa of `A` using Zorn. -/

theorem exists_le_masa (B : NonUnitalStarSubalgebra R A) : ∃ (C : NonUnitalStarSubalgebra R A),
    B ≤ C ∧ C.IsMasa  := by sorry
