import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing A] [StarRing R] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable (hRA : NonUnitalStarSubalgebra R A)

class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm (a b : B)  : a * b = b * a
  maximal :
    ∀ C : NonUnitalStarSubalgebra R A,
      B ≤ C → ∀ (a b : C), a * b = b * a → C ≤ B

/- Need some access lemmas for the above class. -/

/- Let's prove that any commutative `NonUnitalStarSubalgebra` of `A` is contained
in a Masa of `A` using Zorn. -/

theorem exists_le_masa (B : {C : NonUnitalStarSubalgebra R A // (∀ x y : C, x * y = y * x)}) :
    ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa  := by
  have := by
    refine zorn_le (α := {C : NonUnitalStarSubalgebra R A // (∀ x y : C, x * y = y * x) ∧ B ≤ C}) ?_
    intro chain hchain
    have I : Nonempty chain := by sorry
    have J := NonUnitalStarSubalgebra.coe_iSup_of_directed (R := R) (A := A)
      (ι := chain)
      (S := fun chain ↦ chain.1)
    have s := iSup (fun (chain : { C : NonUnitalStarSubalgebra R A //
        (∀ (x y : C), x * y = y * x) ∧ B ≤ C }) ↦ chain.1)
    have hs1 : ∀ (x y : s), x * y = y * x := by sorry
    have hs2 : B ≤ s := sorry
    use ⟨s, hs1, hs2⟩
    refine mem_upperBounds.mpr ?_
    intro x hx
    sorry
  obtain ⟨M, hM⟩ := this
  use M
  constructor
  · sorry
  · sorry
