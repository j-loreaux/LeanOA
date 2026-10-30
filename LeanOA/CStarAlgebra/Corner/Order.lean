module

public import LeanOA.CStarAlgebra.Corner.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

/-! # The order on the corner of a star projection

If `p` is a star projection in an ordered star ring `A`, then the corner `hp.Corner` inherits a
partial order from `A`. When `A` is a non-unital C⋆-algebra with a star-ordered ring structure, so
is the corner `hp.Corner`: an element of the corner is nonnegative in `A` if and only if it is of
the form `star s * s` for some `s` *in the corner*.

## Main declarations

+ `IsStarProjection.Corner.instPartialOrder`: the order on the corner, induced from `A`.
+ `IsStarProjection.Corner.instStarOrderedRing`: if `A` is a non-unital C⋆-algebra which is a
  star-ordered ring, then so is the corner.
-/

variable {A : Type*}

namespace IsStarProjection

namespace Corner

section PartialOrder

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] {p : A} {hp : IsStarProjection p}

instance : PartialOrder hp.Corner := .lift val coe_injective

@[simp, norm_cast]
lemma coe_le_coe {x y : hp.Corner} : (x : A) ≤ y ↔ x ≤ y := .rfl

@[simp, norm_cast]
lemma coe_lt_coe {x y : hp.Corner} : (x : A) < y ↔ x < y := .rfl

@[simp]
lemma zero_le_coe {x : hp.Corner} : 0 ≤ (x : A) ↔ 0 ≤ x := .rfl

@[simp]
lemma coe_le_zero {x : hp.Corner} : (x : A) ≤ 0 ↔ x ≤ 0 := .rfl

lemma monotone_coe : Monotone ((↑) : hp.Corner → A) := fun _ _ ↦ id

lemma strictMono_coe : StrictMono ((↑) : hp.Corner → A) := fun _ _ ↦ id

end PartialOrder

/-- If `A` is a non-unital C⋆-algebra which is a star-ordered ring, then so is the corner
`p * A * p` of a star projection `p`. -/
instance [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p : A}
    {hp : IsStarProjection p} : StarOrderedRing hp.Corner :=
  .of_nonneg_iff'
    (fun h z ↦ by simpa [← coe_le_coe] using add_le_add_left (coe_le_coe.mpr h) (z : A))
    fun x ↦ by
      refine ⟨fun hx ↦ ?_, ?_⟩
      · /- Since `x` commutes with `p`, so does `√x`, and so `s := √x * p` lies in the corner and
        satisfies `star s * s = p * x * p = x`. -/
        rw [← zero_le_coe] at hx
        set q := CFC.sqrt (x : A)
        have hq : Commute q p :=
          Commute.cfcₙ_nnreal ((coe_mul_eq x).trans (mul_coe_eq x).symm) _
        refine ⟨mk hp (q * p) ?_, ext ?_⟩
        · rw [mul_assoc, mul_assoc, hp.isIdempotentElem.eq, ← mul_assoc, ← hq.eq, mul_assoc,
            hp.isIdempotentElem.eq]
        · have hq' : star q = q := (CFC.sqrt_nonneg (x : A)).isSelfAdjoint.star_eq
          simp only [coe_mul, coe_star, coe_mk, star_mul, hq', hp.isSelfAdjoint.star_eq]
          rw [mul_assoc, ← mul_assoc q, CFC.sqrt_mul_sqrt_self _ hx, ← mul_assoc,
            mul_coe_mul_eq]
      · rintro ⟨s, rfl⟩
        simp [← zero_le_coe, star_mul_self_nonneg (s : A)]

end Corner

section toCorner

variable {R : Type*} [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [CommSemiring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {p : A}

variable (R) in
/-- Compression by a star projection is monotone. -/
lemma toCorner_mono (hp : IsStarProjection p) : Monotone (hp.toCorner R) := fun x y h ↦ by
  rw [← Corner.coe_le_coe, coe_toCorner, coe_toCorner]
  simpa [hp.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate h p

end toCorner

end IsStarProjection
