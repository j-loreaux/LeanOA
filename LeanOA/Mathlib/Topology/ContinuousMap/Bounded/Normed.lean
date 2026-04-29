import Mathlib.Topology.ContinuousMap.Bounded.Normed

open BoundedContinuousFunction in
/-- If the product of bounded continuous functions is zero, then the norm of their sum is the
maximum of their norms. -/
lemma BoundedContinuousFunction.norm_add_eq_max {X R : Type*} [TopologicalSpace X] [NormedRing R]
    [IsDomain R] {f g : X →ᵇ R} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  have hfg : ∀ x, f x = 0 ∨ g x = 0 := by simpa [DFunLike.ext_iff, mul_eq_zero] using h
  have hfg' (x : X) : ‖(f + g) x‖ = max ‖f x‖ ‖g x‖ := by obtain (h | h) := hfg x <;> simp [h]
  apply le_antisymm
  · rw [norm_le (by positivity)]
    intro x
    rw [hfg']
    apply max_le <;> exact norm_coe_le_norm _ x |>.trans (by simp)
  · apply max_le
    all_goals
      rw [norm_le (by positivity)]
      intro x
      grw [← (f + g).norm_coe_le_norm x, hfg']
      simp
