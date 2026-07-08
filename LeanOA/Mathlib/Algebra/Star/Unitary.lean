module

public import Mathlib.Algebra.Star.Unitary

public section Unitary

variable {R : Type*} [Monoid R] [StarMul R]

lemma commute_unitary_iff_star_mul_mul {x : R} {u : unitary R} :
    Commute (u : R) x ↔ star u * x * u = x := by
  simpa using! (Unitary.toUnits u).commute_iff_inv_mul_cancel

lemma commute_unitary_iff_star_mul_mul_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ star u * x * u = x :=
  commute_unitary_iff_star_mul_mul (u := ⟨u, hu⟩)

lemma commute_unitary_iff_mul_mul_star {x : R} {u : unitary R} :
    Commute (u : R) x ↔ u * x * star u = x := by
  simpa using! (Unitary.toUnits u).commute_iff_mul_inv_cancel

lemma commute_unitary_iff_mul_mul_star_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ u * x * star u = x :=
  commute_unitary_iff_mul_mul_star (u := ⟨u, hu⟩)

end Unitary
