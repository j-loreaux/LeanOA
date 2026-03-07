import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Order.Bounds.OrderIso
import LeanOA.Mathlib.Order.Hom.Basic

namespace StarOrderedRing
-- maybe this should go in a brand new file in Mathlib to avoid increasing imports?

section NonUnital

variable {R : Type*} [NonUnitalRing R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The map `x ↦ r * x * star r` as an order homomorphism in a star-ordered ring. -/
@[simps]
def conjOrderHom (r : R) : R →o R where
  toFun x := r * x * star r
  monotone' _ _ h := star_right_conjugate_le_conjugate h r

lemma conjOrderHom_mul (r s : R) :
    conjOrderHom (r * s) = (conjOrderHom r).comp (conjOrderHom s) := by
  ext; simp [mul_assoc]

/-- The map `r x ↦ r * x * star r` as a semigroup homomorphism from `R` into `R →o R`. -/
@[simps]
def conjOrderHomMulHom : R →ₙ* R →o R where
  toFun := conjOrderHom
  map_mul' := conjOrderHom_mul

end NonUnital

section Unital

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

@[simp]
lemma conjOrderHom_one : conjOrderHom (1 : R) = .id := by ext; simp

/-- The map `r x ↦ r * x * star r` as a monoid homomorphism from `R` into `R →o R`. -/
@[simps]
def conjOrderHomMonoidHom : R →* R →o R where
  toFun := conjOrderHom
  map_mul' := conjOrderHom_mul
  map_one' := conjOrderHom_one

@[simp]
lemma toMulHom_conjOrderHomMonoidHom :
    (conjOrderHomMonoidHom (R := R)).toMulHom = conjOrderHomMulHom :=
  rfl

/-- The map  `r x ↦ r * x * star r` as a group homomorphism from `Rˣ` into `R ≃o R`
in a star-ordered ring `R`. -/
def conjUnitsOrderIso : Rˣ →* (R ≃o R) where
  toFun r := .ofHomInv' (conjOrderHomMonoidHom (r : R)) (conjOrderHomMonoidHom (↑r⁻¹ : R))
    (by rw [← OrderHom.mul_eq_comp, ← map_mul]; simp)
    (by rw [← OrderHom.mul_eq_comp, ← map_mul]; simp)
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

lemma _root_.IsLUB.conjugate_star_right_of_isUnit {s : Set R} {x : R}
      (h : IsLUB s x) (r : R) (hr : IsUnit r) :
    IsLUB (conjOrderHom r '' s) (r * x * star r) := by
  lift r to Rˣ using hr
  exact (conjUnitsOrderIso r).isLUB_image'.mpr h

end Unital

--- we could also turn `conjOrderHom` into a `PositiveLinearMap`, which we should do.
end StarOrderedRing
