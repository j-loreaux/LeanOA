module

public import LeanOA.Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

@[expose] public section

section IsSelfAdjoint

open CStarAlgebra Metric Set
open scoped Pointwise

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma isSelfAdjoint_and_norm_le_iff {x : A} {r : ℝ} :
    IsSelfAdjoint x ∧ ‖x‖ ≤ r ↔ ∃ y z, (0 ≤ y ∧ ‖y‖ ≤ r) ∧ (0 ≤ z ∧ ‖z‖ ≤ r) ∧ x = y - z := by
  constructor
  · rintro ⟨hx, hxr⟩
    exact ⟨x⁺, x⁻,
      ⟨by cfc_tac, (norm_posPart_le x).trans hxr⟩,
      ⟨by cfc_tac, (norm_negPart_le x).trans hxr⟩,
      (CFC.posPart_sub_negPart _ hx).symm⟩
  · rintro ⟨y, z, ⟨hy, hyr⟩, ⟨hz, hzr⟩, rfl⟩
    refine ⟨by cfc_tac, ?_⟩
    grw [CStarAlgebra.norm_sub_le_max_of_nonneg hy hz, hyr, hzr, max_self]

lemma isSelfAdjoint_and_norm_lt_iff {x : A} {r : ℝ} :
    IsSelfAdjoint x ∧ ‖x‖ < r ↔ ∃ y z, (0 ≤ y ∧ ‖y‖ < r) ∧ (0 ≤ z ∧ ‖z‖ < r) ∧ x = y - z := by
  constructor
  · rintro ⟨hx, hxr⟩
    exact ⟨x⁺, x⁻,
      ⟨by cfc_tac, (norm_posPart_le x).trans_lt hxr⟩,
      ⟨by cfc_tac, (norm_negPart_le x).trans_lt hxr⟩,
      (CFC.posPart_sub_negPart _ hx).symm⟩
  · rintro ⟨y, z, ⟨hy, hyr⟩, ⟨hz, hzr⟩, rfl⟩
    refine ⟨by cfc_tac, ?_⟩
    grw [IsSelfAdjoint.norm_le_max_of_le_of_le (a := -z) (c := y) (by simpa) (by simpa)]
    simp_all

lemma setOfPred_isSelfAdjoint_inter_closedBall_eq {r : ℝ} :
    {x : A | IsSelfAdjoint x} ∩ closedBall 0 r =
      {x | 0 ≤ x} ∩ closedBall 0 r - {x | 0 ≤ x} ∩ closedBall 0 r := by
  ext
  simp [isSelfAdjoint_and_norm_le_iff, Set.mem_sub]
  grind

lemma setOfPred_isSelfAdjoint_inter_ball_eq {r : ℝ} :
    {x : A | IsSelfAdjoint x} ∩ ball 0 r = {x | 0 ≤ x} ∩ ball 0 r - {x | 0 ≤ x} ∩ ball 0 r := by
  ext
  simp [isSelfAdjoint_and_norm_lt_iff, Set.mem_sub]
  grind

end IsSelfAdjoint
