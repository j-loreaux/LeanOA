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
