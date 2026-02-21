import Mathlib.Analysis.InnerProductSpace.Basic
import LeanOA.Mathlib.Analysis.Normed.Extreme

open Set Metric RCLike
open scoped ComplexOrder InnerProductSpace

/-- In a nontrivial Hilbert space, the extreme points of the closed unit ball is exactly the unit
sphere. -/
theorem InnerProductSpace.extremePoints_closedUnitBall_eq_unitSphere {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Nontrivial E] :
    extremePoints 𝕜 (closedBall (0 : E) 1) = sphere 0 1 := by
  apply subset_antisymm extremePoints_closedUnitBall_subset_unitSphere
  simp only [subset_def, mem_extremePoints, mem_sphere, dist_zero_right, mem_closedBall]
  refine fun x hx ↦ ⟨hx.le, fun y hy z hz ⟨a, b, ha, hb, hab, hxyz⟩ ↦ ?_⟩
  rw [pos_iff, ← conj_eq_iff_im, conj_eq_iff_re] at ha hb
  rw [← ha.2, ← hb.2, ← ofReal_add, ← ofReal_one, ofReal_inj] at hab
  set a' : ℝ := re a
  set b' : ℝ := re b
  if hyz : y = z then simp_all else
  by_cases H : ‖y‖ = 1 ∧ ‖z‖ = 1
  · have H' : re ⟪y, z⟫_𝕜 < 1 := by
      refine lt_iff_le_and_ne.mpr ⟨re_inner_le_norm y z |>.trans (by simp [H]), ?_⟩
      rw [← real_inner_eq_re_inner, ne_eq]
      exact @inner_eq_one_iff_of_norm_eq_one _ _ _ _ (.rclikeToReal 𝕜 E) _ _ H.1 H.2 |>.not.mpr hyz
    have := calc 1 = ‖x‖ ^ 2 := by rw [hx, one_pow]
      _ = a' ^ 2 • ‖y‖ ^ 2 + 2 * a' * b' * re ⟪y, z⟫_𝕜 + b' ^ 2 * ‖z‖ ^ 2 := by
        rw [← hxyz, norm_add_pow_two (𝕜 := 𝕜)]
        simp [norm_smul, mul_pow, inner_smul_left, inner_smul_right, ← ha.2, ← hb.2]
        ring
      _ < a' ^ 2 + 2 * a' * b' * 1 + b' ^ 2 := by
        conv_lhs => simp only [H, one_pow, smul_eq_mul, mul_one]
        simp only [add_lt_add_iff_right, add_lt_add_iff_left]
        exact mul_lt_mul_of_pos_left H' <| mul_pos (mul_pos two_pos ha.1) hb.1
      _ = 1 := by simp [← add_sq, hab]
    grind
  · obtain (h | h) := not_and_or.mp H
    on_goal 1 => have Hy : ‖y‖ < 1 := by grind
    on_goal 2 => have Hz : ‖z‖ < 1 := by grind
    all_goals
      have := calc 1 = ‖x‖ := hx.symm
        _ ≤ a' * ‖y‖ + b' * ‖z‖ := by
          grw [← hxyz, norm_add_le]
          simp [norm_smul, ← ha.2, ← hb.2, norm_of_nonneg ha.1.le, norm_of_nonneg hb.1.le]
        _ < a' * 1 + b' * 1 := ?_
        _ = 1 := by simp [hab]
      grind
    · exact add_lt_add_of_lt_of_le (mul_lt_mul' le_rfl Hy (norm_nonneg _) ha.1)
        (mul_le_mul_of_nonneg_left hz hb.1.le)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hy ha.1.le)
        (mul_lt_mul' le_rfl Hz (norm_nonneg _) hb.1)
