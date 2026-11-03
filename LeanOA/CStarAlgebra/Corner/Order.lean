module

public import LeanOA.CStarAlgebra.Corner.Basic
public import LeanOA.Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

/-! # The order on the corner of a star projection

If `p` is a star projection in an ordered star ring `A`, then the corner `hp.Corner` inherits a
partial order from `A`. When `A` is a star-ordered ring with a real non-unital continuous
functional calculus (e.g., a non-unital C⋆-algebra), so is the corner `hp.Corner`: an element of
the corner is nonnegative in `A` if and only if it is of the form `star s * s` for some `s` *in the
corner*.

## Main declarations

+ `IsStarProjection.Corner.instPartialOrder`: the order on the corner, induced from `A`.
+ `IsStarProjection.Corner.coeOrderEmbedding`: the inclusion of the corner into `A`, as an order
  embedding.
+ `IsStarProjection.Corner.instStarOrderedRing`: if `A` is a star-ordered ring with a real
  non-unital continuous functional calculus, then so is the corner.
-/

variable {A : Type*}

namespace IsStarProjection

namespace Corner

section PartialOrder

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] {p : A} {hp : IsStarProjection p}

instance : PartialOrder hp.Corner := .lift val coe_injective

variable (hp) in
/-- The inclusion of the corner `p * A * p` into `A`, as an order embedding. -/
def coeOrderEmbedding : hp.Corner ↪o A where
  toFun := (↑)
  inj' := coe_injective
  map_rel_iff' := .rfl

@[simp]
lemma coe_coeOrderEmbedding : ⇑(coeOrderEmbedding hp) = (↑) := rfl

@[simp, norm_cast]
lemma coe_le_coe {x y : hp.Corner} : (x : A) ≤ y ↔ x ≤ y := (coeOrderEmbedding hp).le_iff_le

@[simp, norm_cast]
lemma coe_lt_coe {x y : hp.Corner} : (x : A) < y ↔ x < y := (coeOrderEmbedding hp).lt_iff_lt

@[simp]
lemma zero_le_coe {x : hp.Corner} : 0 ≤ (x : A) ↔ 0 ≤ x := by rw [← coe_le_coe, coe_zero]

@[simp]
lemma coe_le_zero {x : hp.Corner} : (x : A) ≤ 0 ↔ x ≤ 0 := by rw [← coe_le_coe, coe_zero]

lemma monotone_coe : Monotone ((↑) : hp.Corner → A) := (coeOrderEmbedding hp).monotone

lemma strictMono_coe : StrictMono ((↑) : hp.Corner → A) := (coeOrderEmbedding hp).strictMono

end PartialOrder

/-- If `A` is a star-ordered ring with a real non-unital continuous functional calculus (e.g., a
non-unital C⋆-algebra), then so is the corner `p * A * p` of a star projection `p`. -/
instance instStarOrderedRing [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] {p : A} {hp : IsStarProjection p} : StarOrderedRing hp.Corner :=
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

section Projection

/-! ### Projections in the corner

The projections in the corner of `p` are exactly the projections `q ≤ p` of `A`. -/

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {p : A}
  {hp : IsStarProjection p}

/-- A projection in the corner of `p` is a subprojection of `p`. -/
lemma coe_le_of_isStarProjection {q : hp.Corner} (hq : IsStarProjection q) : (q : A) ≤ p := by
  have := coe_le_coe.mpr hq.le_one
  rwa [coe_one] at this

/-- The projections in the corner of `p` are exactly the subprojections of `p`. -/
lemma exists_isStarProjection_coe_eq_iff {q : A} :
    (∃ q' : hp.Corner, IsStarProjection q' ∧ (q' : A) = q) ↔ IsStarProjection q ∧ q ≤ p := by
  refine ⟨?_, fun ⟨hq, hqp⟩ ↦ ⟨mk hp q (hq.mul_mul_eq_of_le hp hqp), ?_, rfl⟩⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨isStarProjection_coe_iff.mpr hq, coe_le_of_isStarProjection hq⟩
  · rwa [← isStarProjection_coe_iff, coe_mk]

end Projection

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
