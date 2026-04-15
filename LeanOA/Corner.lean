import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Algebra.Star.StarProjection

open Set

namespace NonUnitalStarSubalgebra

open NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarRing A]

variable (R) in
/-- The non-unital star-subalgebra `a * A * star a` of `A` given by compression to the corner. -/
@[simps]
def corner (a : A) : NonUnitalStarSubalgebra R A where
  carrier := Set.range (a * · * star a)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by simp only [mul_add, add_mul]⟩
  smul_mem' r := by
    rintro - ⟨x, rfl⟩
    exact ⟨r • x, by simp only [← smul_mul_assoc, mul_smul_comm]⟩
  mul_mem' := by
    rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * star a * a * y, by simp only [mul_assoc]⟩
  star_mem' := by
    rintro - ⟨x, rfl⟩
    exact ⟨star x, by simp [mul_assoc]⟩

lemma mem_corner_iff {a x : A} : x ∈ corner R a ↔ ∃ y, a * y * star a = x := Iff.rfl

lemma IsSelfAdjoint.mem_corner_ifff {a : A} (ha : IsSelfAdjoint a) {x : A} :
    x ∈ corner R a ↔ ∃ y, a * y * a = x := by
  simp only [mem_corner_iff, ha.star_eq]

variable (R) in
lemma mem_corner (a x : A) : a * x * star a ∈ corner R a := ⟨x, rfl⟩

variable (R) in
lemma IsSelfAdjoint.mem_corner {a : A} (ha : IsSelfAdjoint a) (x : A) :
    a * x * a ∈ corner R a := by
  simpa [ha.star_eq] using NonUnitalStarSubalgebra.mem_corner R a x

end NonUnitalStarSubalgebra
