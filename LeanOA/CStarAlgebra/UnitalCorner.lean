module

public import LeanOA.Corner
public import LeanOA.Ultraweak.Masa
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Star.StarProjection

@[expose] public section

/-! # The corner of a C⋆-algebra by a projection is a unital C⋆-algebra

If `p` is a projection in a C⋆-algebra `A`, the corner `p * A * p` is a closed non-unital
star subalgebra of `A`, and `p` is a unit for it. This file provides the resulting unital
structures, with the unit given *by definition* as `p`.

These are not instances, because they depend on the proof that `p` is a projection; they are meant
to be used locally, e.g., via `letI := hp.cornerCStarAlgebra`.
-/

open NonUnitalStarSubalgebra

lemma IsStarProjection.mem_corner_iff' {A : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {p : A} (hp : IsStarProjection p)
    {x : A} : x ∈ corner ℂ p ↔ p * x * p = x := by
  rw [hp.isSelfAdjoint.mem_corner_iff]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [← mul_assoc, hp.isIdempotentElem.eq]
    rw [mul_assoc _ p p, hp.isIdempotentElem.eq]
  · exact fun h ↦ ⟨x, h⟩

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)
include hp

namespace IsStarProjection

lemma isClosed_corner : IsClosed (corner ℂ p : Set A) := by
  have : (corner ℂ p : Set A) = {x | p * x * p = x} := Set.ext fun x ↦ hp.mem_corner_iff'
  rw [this]
  exact isClosed_eq (by fun_prop) continuous_id

lemma mul_mul_mem_corner (x : A) : p * x * p ∈ corner ℂ p :=
  ⟨x, by rw [hp.isSelfAdjoint.star_eq]⟩

lemma self_mem_corner : p ∈ corner ℂ p := by
  simpa [hp.isIdempotentElem.eq] using hp.mul_mul_mem_corner 1

lemma mul_eq_of_mem_corner {x : A} (hx : x ∈ corner ℂ p) : p * x = x := by
  rw [← hp.mem_corner_iff'.mp hx]
  simp only [← mul_assoc, hp.isIdempotentElem.eq]

lemma mul_eq_of_mem_corner' {x : A} (hx : x ∈ corner ℂ p) : x * p = x := by
  rw [← hp.mem_corner_iff'.mp hx, mul_assoc, hp.isIdempotentElem.eq]

/-- The multiplicative structure on the corner `p * A * p` with unit `p`. -/
noncomputable abbrev cornerMulOneClass : MulOneClass (corner ℂ p) where
  one := ⟨p, hp.self_mem_corner⟩
  one_mul x := Subtype.ext <| hp.mul_eq_of_mem_corner x.2
  mul_one x := Subtype.ext <| hp.mul_eq_of_mem_corner' x.2

/-- The ring structure on the corner `p * A * p` with unit `p`. -/
noncomputable abbrev cornerRing : Ring (corner ℂ p) :=
  letI := hp.cornerMulOneClass
  { (inferInstance : NonUnitalRing (corner ℂ p)), hp.cornerMulOneClass with }

/-- The algebra structure on the corner `p * A * p` with unit `p`. -/
noncomputable abbrev cornerAlgebra :
    letI := hp.cornerRing
    Algebra ℂ (corner ℂ p) :=
  letI := hp.cornerRing
  .ofModule smul_mul_assoc mul_smul_comm

/-- The corner `p * A * p` is a C⋆-algebra with unit `p`. -/
noncomputable abbrev cornerCStarAlgebra : CStarAlgebra (corner ℂ p) :=
  haveI := hp.isClosed_corner
  letI := hp.cornerRing
  letI := hp.cornerAlgebra
  { (inferInstance : NonUnitalCStarAlgebra (corner ℂ p)), hp.cornerRing, hp.cornerAlgebra with }

lemma coe_one_cornerCStarAlgebra :
    letI := hp.cornerCStarAlgebra
    ((1 : corner ℂ p) : A) = p :=
  rfl

end IsStarProjection
