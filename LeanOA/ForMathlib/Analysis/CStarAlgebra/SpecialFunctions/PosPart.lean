/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-! # C⋆-algebraic facts about `a⁺` and `a⁻`.

-/

variable {A : Type*}

namespace CStarAlgebra

section Norm

variable [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [StarRing A]
variable [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

@[simp]
lemma norm_posPart_le (a : A) : ‖a⁺‖ ≤ ‖a‖ := by
  refine (em (IsSelfAdjoint a)).elim (fun ha ↦ ?_)
    fun ha ↦ by simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx ↦ ?_
  obtain (h | h) := le_or_lt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hx ha

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

end CStarAlgebra
