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

open Unitization in
/-- If `e` is an element of the nonnegative closed unit ball, then `e * e ≤ e`, with equality
if `e` is an extreme point
(see `isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall`). -/
lemma CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e * e ≤ e := by
  rw [← inr_le_iff (e * e) e, inr_mul, ← sub_nonneg, ← mul_one_sub]
  exact ((Commute.one_right _).sub_right (.refl _)).mul_nonneg he0.inr
    (sub_nonneg.mpr (CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he0, he1⟩).2)
