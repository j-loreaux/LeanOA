import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.RCLike.Basic

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ComplexOrder Set Metric

theorem subsingleton_of_zero_mem_extremePoints_closedUnitBall
    (h : 0 ∈ extremePoints 𝕜 (closedBall (0 : H) 1)) : Subsingleton H := by
  by_contra!
  obtain ⟨y, hy⟩ := exists_ne (0 : H)
  set z := (1 / ‖y‖ : 𝕜) • y
  have hz : z ∈ closedBall (0 : H) 1 ∧ ‖z‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy, z]
  simp only [mem_extremePoints, mem_closedBall, dist_zero_right] at h
  have := h.2 z hz.2.le (-z) (norm_neg z ▸ hz.2.le) ⟨1 / 2, ⟨1 / 2, by simp [-one_div]⟩⟩
  simp_all

theorem norm_eq_one_of_mem_extremePoints_closedUnitBall [Nontrivial H] {x : H}
    (hx : x ∈ extremePoints 𝕜 (closedBall (0 : H) 1)) : ‖x‖ = 1 := by
  have h : x ≠ 0 := fun h ↦
    have := subsingleton_of_zero_mem_extremePoints_closedUnitBall (h ▸ hx)
    false_of_nontrivial_of_subsingleton H
  simp only [mem_extremePoints, mem_closedBall, dist_zero_right] at hx
  by_contra!
  refine h (@hx.2 ((1 / ‖x‖ : 𝕜) • x) ?_ 0 (by simp) ⟨‖x‖, 1 - ‖x‖, by simp_all, ?_, ?_⟩).2.symm
  on_goal 2 => rw [sub_pos, ← RCLike.ofReal_one (K := 𝕜), RCLike.ofReal_lt_ofReal]; grind
  all_goals simp [norm_smul, norm_ne_zero_iff.mpr h]

/-- In a nontrivial normed space, the extreme points of the closed unit ball is contained in
the unit sphere. -/
lemma extremePoints_closedUnitBall_subset_unitSphere [Nontrivial H] :
    extremePoints 𝕜 (closedBall (0 : H) 1) ⊆ sphere 0 1 :=
  fun _ hx ↦ by simpa using norm_eq_one_of_mem_extremePoints_closedUnitBall hx
