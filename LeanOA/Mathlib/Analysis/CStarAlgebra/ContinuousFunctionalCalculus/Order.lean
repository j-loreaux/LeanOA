import LeanOA.Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

variable {ι A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `x : ι → A` is summable and `y` is dominated by `x` (i.e., `0 ≤ y i ≤ x i` for `i : ι`), then
`y` is also summable. -/
lemma CStarAlgebra.dominated_convergence {x y : ι → A} (hx : Summable x)
    (hy_nonneg : ∀ i, 0 ≤ y i) (h_le : ∀ i, y i ≤ x i) : Summable y := by
  rw [summable_iff_vanishing] at hx ⊢
  intro u hu
  obtain ⟨ε, ε_pos, hε⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hu
  specialize hx (Metric.closedBall 0 ε) (Metric.closedBall_mem_nhds 0 ε_pos)
  peel hx with s t hst _
  refine hε ?_
  simp only [Metric.mem_closedBall, dist_zero_right] at this ⊢
  refine le_trans ?_ this
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (t.sum_nonneg fun i _ ↦ (hy_nonneg i)) ?_
  gcongr
  exact h_le _

alias ⟨LE.le.of_inr, LE.le.inr⟩ := Unitization.inr_nonneg_iff

open CStarAlgebra Unitization CFC in
lemma IsStarProjection.mul_right_eq_self_of_nonneg_of_le {a e : A} (he : IsStarProjection e)
    (ha : 0 ≤ a) (hae : a ≤ e) : a * e = a := by
  suffices ‖star (sqrt a * (1 - e : A⁺¹)) * (sqrt a * (1 - e))‖ = 0 by
    rw [CStarRing.norm_star_mul_self, mul_eq_zero, norm_eq_zero, or_self, mul_sub, sub_eq_zero,
      mul_one, ← inr_mul, inr_injective.eq_iff] at this
    rw [nonneg_iff_eq_sqrt_mul_sqrt.mp ha, mul_assoc, ← this]
  simp only [star_mul, star_sub, star_one, (sqrt_nonneg a).inr.star_eq, mul_assoc, norm_eq_zero]
  simp_rw [← mul_assoc ((sqrt a : A) : A⁺¹), ← inr_mul, ← nonneg_iff_eq_sqrt_mul_sqrt.mp ha]
  nth_rw 1 [← star_one, ← star_sub, ← mul_assoc]
  apply le_antisymm (le_of_le_of_eq (star_left_conjugate_le_conjugate
    (inr_le_iff a e |>.mpr hae) _) _) (star_left_conjugate_nonneg (by simpa) _)
  simp [mul_assoc, (he.inr (R := ℂ)).mul_one_sub_self]

lemma IsStarProjection.conjugate_of_nonneg_of_le {a e : A} (he : IsStarProjection e)
    (ha : 0 ≤ a) (hae : a ≤ e) : e * a * e = a := by
  have := he.mul_right_eq_self_of_nonneg_of_le ha hae
  rwa [mul_assoc, this, ← he.2, ← star_star a, ← star_mul, star_inj, ha.star_eq]
