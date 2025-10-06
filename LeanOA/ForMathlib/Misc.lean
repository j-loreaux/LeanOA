import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Sqrt

-- goes in `Data.Complex.Basic`
lemma Complex.normSq_ofReal_add_I_smul_sqrt_one_sub {x : ℝ} (hx : ‖x‖ ≤ 1) :
    normSq (x + I * √(1 - x ^ 2)) = 1 := by
  simp [mul_comm I, normSq_add_mul_I,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]

-- goes in `Analysis.CStarAlgebra.Basic`
theorem IsSelfAdjoint.sq_norm {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {x : E} (hx : IsSelfAdjoint x) :
    ‖x ^ 2‖ = ‖x‖ ^ 2 := by
  simpa using congr(($(hx.nnnorm_pow_two_pow 1) : ℝ))

-- `Mathlib.Data.Complex.Module`
open scoped ComplexStarModule in
@[simp]
theorem selfAdjoint.realPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] (a : selfAdjoint A) :
    ℜ (a : A) = a :=
  Subtype.ext a.2.coe_realPart

-- `Analysis.Normed.Module.Basic`
@[simp]
lemma norm_smul_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    ‖x‖ • ‖x‖⁻¹ • x = x := by
  obtain (rfl | hx) := eq_zero_or_norm_pos x
  · simp
  · simp [hx.ne']

-- `Mathlib.Analysis.SpecialFunctions.Complex.Arg`
@[fun_prop]
theorem Complex.continuousOn_arg : ContinuousOn arg slitPlane :=
  fun _ h ↦ continuousAt_arg h |>.continuousWithinAt

open Complex in
lemma spectrum_subset_slitPlane_of_norm_lt_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u - 1‖ < 1) :
    spectrum ℂ u ⊆ slitPlane := by
  have := spectrum.subset_closedBall_norm (𝕜 := ℂ) (u - 1) |>.trans <|
    Metric.closedBall_subset_ball hu
  rw [← map_one (algebraMap ℂ A), ← spectrum.sub_singleton_eq, Set.sub_singleton] at this
  exact fun x hx ↦ add_sub_cancel 1 x ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using this ⟨x, hx, rfl⟩)
