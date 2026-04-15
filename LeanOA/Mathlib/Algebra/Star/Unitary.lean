module

public import Mathlib.Algebra.Star.Unitary

public section Unitary

variable {R : Type*} [Monoid R] [StarMul R]

lemma Unitary.commute_self_star (u : unitary R) : Commute u (star u) := by simp [commute_iff_eq]
lemma Unitary.commute_star_self (u : unitary R) : Commute (star u) u := by simp [commute_iff_eq]

lemma commute_unitary_self_star {u : R} (hu : u ∈ unitary R) : Commute u (star u) := by
  simpa only [commute_iff_eq, Subtype.ext_iff, Submonoid.coe_mul, Unitary.coe_star] using
    Unitary.commute_self_star ⟨u, hu⟩

lemma commute_unitary_star_self {u : R} (hu : u ∈ unitary R) : Commute (star u) u :=
  commute_unitary_self_star hu |>.symm

lemma commute_unitary_iff_star_mul_mul {x : R} {u : unitary R} :
    Commute (u : R) x ↔ star u * x * u = x := by
  simpa using (Unitary.toUnits u).commute_iff_inv_mul_cancel

lemma commute_unitary_iff_star_mul_mul_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ star u * x * u = x :=
  commute_unitary_iff_star_mul_mul (u := ⟨u, hu⟩)

lemma commute_unitary_iff_mul_mul_star {x : R} {u : unitary R} :
    Commute (u : R) x ↔ u * x * star u = x := by
  simpa using (Unitary.toUnits u).commute_iff_mul_inv_cancel

lemma commute_unitary_iff_mul_mul_star_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ u * x * star u = x :=
  commute_unitary_iff_mul_mul_star (u := ⟨u, hu⟩)

end Unitary
