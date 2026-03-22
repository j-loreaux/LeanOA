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

open Unitization NNReal CStarAlgebra in
lemma CStarAlgebra.nnrpow_le_self_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn : 1 ≤ n) : e ^ n ≤ e := by
  have : n ≠ 0 := by aesop
  rw [← inr_le_iff (e ^ _) e, CFC.nnrpow_eq_cfcₙ_real e, cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..]
  conv_rhs => rw [← cfc_id' ℝ (e : A⁺¹)]
  rw [← sub_nonneg, ← cfc_sub ..]
  refine cfc_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := spectrum.norm_le_norm_of_mem hx
  grw [norm_inr, he1, Real.norm_eq_abs] at this
  exact Real.rpow_le_self_of_le_one (spectrum_nonneg_of_nonneg he0.inr hx) (by grind) hn

/-- If `e` is an element of the nonnegative closed unit ball, then `e * e ≤ e`, with equality
if `e` is an extreme point
(see `isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall`). -/
lemma CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e * e ≤ e := CFC.nnrpow_two e ▸ nnrpow_le_self_of_nonneg_of_norm_le_one he0 he1 one_le_two

open Unitization NNReal CStarAlgebra in
lemma CStarAlgebra.self_le_nnrpow_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn0 : n ≠ 0) (hn : n ≤ 1) : e ≤ e ^ n := by
  rw [← inr_le_iff e (e ^ _), CFC.nnrpow_eq_cfcₙ_real e, cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..]
  conv_lhs => rw [← cfc_id' ℝ (e : A⁺¹)]
  rw [← sub_nonneg, ← cfc_sub ..]
  refine cfc_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := spectrum.norm_le_norm_of_mem hx
  grw [norm_inr, he1, Real.norm_eq_abs] at this
  exact Real.self_le_rpow_of_le_one (spectrum_nonneg_of_nonneg he0.inr hx) (by grind) hn

lemma CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e ≤ CFC.sqrt e :=
  CFC.sqrt_eq_nnrpow e ▸ self_le_nnrpow_of_nonneg_of_norm_le_one he0 he1 (by simp) (by simp)
