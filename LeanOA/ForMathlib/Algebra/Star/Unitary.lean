import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.ContinuousFunctionalCalculus

variable {A : Type*} [Monoid A] [StarMul A]

/-- In a star monoid, the product `a * b⁻¹` of units is unitary if `star a * a = star b * b`. -/
lemma Units.mul_inv_mem_unitary (a b : Aˣ)
    (hab : star a * a = star b * b) : (a * b⁻¹ : A) ∈ unitary A := by
  apply IsUnit.mem_unitary_of_star_mul_self (by aesop)
  have : (star a : A) * a = (star b : A) * b := congr(($(hab) : A))
  rw [star_mul, mul_assoc, ← mul_assoc (star a : A), this]
  simp [mul_assoc, ← Units.coe_star_inv]

/-- In a star monoid, the product `a⁻¹ * b` of units is unitary if `a * star a = b * star b`. -/
lemma Units.inv_mul_mem_unitary (a b : Aˣ)
    (hab : a * star a = b * star b) : (a⁻¹ * b : A) ∈ unitary A :=
  inv_inv b ▸ a⁻¹.mul_inv_mem_unitary b⁻¹ (by simpa [← mul_inv_rev])

@[simp]
lemma one_mem_unitary : 1 ∈ unitary A :=
  one_mem _

attribute [aesop 10% apply (rule_sets := [CStarAlgebra])] isStarNormal_of_mem_unitary
