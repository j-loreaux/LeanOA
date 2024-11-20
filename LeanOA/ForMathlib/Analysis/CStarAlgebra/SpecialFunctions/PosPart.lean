/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # C⋆-algebraic facts about `a⁺` and `a⁻`.

[PR #18056](https://github.com/leanprover-community/mathlib4/pull/18506) upstreams the material about `span` to Mathlib.
-/

variable {A : Type*}

namespace CStarAlgebra

section Norm

variable [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [RegularNormedAlgebra ℝ A] [StarRing A] [CompleteSpace A]
variable [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

@[simp]
lemma norm_posPart_le (a : A) : ‖a⁺‖ ≤ ‖a‖ := by
  refine norm_cfcₙ_le fun x hx ↦ ?_
  obtain (h | h) := le_or_lt x 0
  · simp [_root_.posPart_def, max_eq_right h]
  · simp only [_root_.posPart_def, max_eq_left h.le]
    rw [Unitization.quasispectrum_eq_spectrum_inr] at hx
    rw [← Unitization.norm_inr (𝕜 := ℝ) a]
    exact spectrum.norm_le_norm_of_mem hx

@[simp]
lemma norm_negPart_le (a : A) : ‖a⁻‖ ≤ ‖a‖ := by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

lemma _root_.IsSelfAdjoint.norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ := by
  refine le_antisymm ?_ <| max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' ℝ a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx']
  · apply le_max_of_le_right
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [negPart_eq_neg.mpr hx', norm_neg]

end Norm

section SpanNonneg

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Submodule

/-- A C⋆-algebra is spanned by nonnegative elements of norm at most `r` -/
lemma span_nonneg_inter_closedBall {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg, span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : ℂ)⁻¹ • ((r * ‖x‖⁻¹ : ℂ) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity

/-- A C⋆-algebra is spanned by nonnegative elements of norm less than `r`. -/
lemma span_nonneg_inter_ball {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
  exact Metric.closedBall_subset_ball <| half_lt_self hr

/-- A C⋆-algebra is spanned by nonnegative contractions. -/
lemma span_nonneg_inter_unitClosedBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 1) = ⊤ :=
  span_nonneg_inter_closedBall zero_lt_one

/-- A C⋆-algebra is spanned by nonnegative strict contractions. -/
lemma span_nonneg_inter_unitBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) = ⊤ :=
  span_nonneg_inter_ball zero_lt_one

end SpanNonneg

end CStarAlgebra
