module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

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
  refine CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_ (t.sum_nonneg fun i _ ↦ (hy_nonneg i))
  gcongr
  exact h_le _

open Metric Set in
lemma IsStarProjection.mem_image_mul_mul_nonneg_inter_unitClosedBall_iff
    {e : A} (he : IsStarProjection e) :
    (e * · * e) '' ({x | 0 ≤ x} ∩ closedBall 0 1) = Icc 0 e ∩ closedBall 0 1 := by
  ext x
  constructor
  · rintro ⟨x, ⟨hx₀, hx₁⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [mem_closedBall, dist_zero_right] at hx₁ ⊢
    · exact he.isSelfAdjoint.conjugate_nonneg hx₀
    · rw (occs := [1]) [← he.isSelfAdjoint.star_eq]
      grw [CStarAlgebra.star_left_conjugate_le_norm_smul ..,
        he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, hx₁, one_smul]
      exact he.nonneg
    · grw [norm_mul₃_le, hx₁, he.norm_le]
      simpa using he.norm_le
  · rintro ⟨⟨hx₀, hxe⟩, hx₁⟩
    exact ⟨x, ⟨hx₀, hx₁⟩, he.conjugate_of_nonneg_of_le hx₀ hxe⟩
