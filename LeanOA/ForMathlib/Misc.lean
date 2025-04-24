import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Sqrt

-- goes in `Data.Complex.Basic`
lemma Complex.normSq_ofReal_add_I_smul_sqrt_one_sub {x : ℝ} (hx : ‖x‖ ≤ 1) :
    normSq (x + I * √(1 - x ^ 2)) = 1 := by
  simp [mul_comm I, normSq_add_mul_I, ← ofReal_pow,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]

-- goes in `Analysis.CStarAlgebra.Basic`
theorem IsSelfAdjoint.sq_norm {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {x : E} (hx : IsSelfAdjoint x) :
    ‖x ^ 2‖ = ‖x‖ ^ 2 := by
  simpa using congr(($(hx.nnnorm_pow_two_pow 1) : ℝ))

open scoped ComplexStarModule in
@[simp]
theorem selfAdjoint.realPart {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] (a : selfAdjoint A) :
    ℜ (a : A) = a :=
  Subtype.ext a.2.coe_realPart

@[simp]
lemma norm_smul_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    ‖x‖ • ‖x‖⁻¹ • x = x := by
  obtain (rfl | hx) := eq_zero_or_norm_pos x
  · simp
  · simp [hx.ne']
