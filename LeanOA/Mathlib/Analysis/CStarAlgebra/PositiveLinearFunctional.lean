import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma PositiveLinearMap.norm_apply_le (f : A →ₚ[ℂ] ℂ) (x : A) : ‖f x‖ ≤ (f 1).re * ‖x‖ := by
  rw [← sq_le_sq₀ (by positivity) (mul_nonneg (Complex.nonneg_iff.mp
      (f.map_nonneg zero_le_one) |>.1) (by positivity))]
  calc
    _ ≤ (f 1).re * (f (star x * x)).re := by
      have (x y : A) : ‖f (star x * y)‖ ^ 2 ≤ (f (star x * x)).re * (f (star y * y)).re := by
        simpa [← inner_conj_symm (f.toPreGNS y) (f.toPreGNS x), Complex.star_def, norm_star,
            ← sq, f.preGNS_inner_def, ← Complex.ofReal_pow, f.preGNS_norm_def, Real.sq_sqrt,
            Complex.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _))] using
          inner_mul_inner_self_le (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)
      simpa using this 1 x
    _ ≤ (f 1).re * (‖x‖ ^ 2 * (f 1).re) := by
      refine mul_le_mul_of_nonneg_left ?_ (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one) |>.1)
      have := by simpa [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one, ← sq] using
        f.apply_le_of_isSelfAdjoint _ (.star_mul_self x)
      convert Complex.le_def.mp this |>.1
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
    _ = _ := by ring

theorem PositiveLinearMap.norm_map_one (f : A →ₚ[ℂ] ℂ) : ‖f 1‖ = (f 1).re := by
  by_cases! Subsingleton A
  · simp [Subsingleton.eq_zero (1 : A)]
  exact le_antisymm (by simpa using f.norm_apply_le 1) (Complex.re_le_norm _)

theorem PositiveLinearMap.opNorm_eq_re_map_one (f : A →ₚ[ℂ] ℂ) :
    ‖f.toContinuousLinearMap‖ = (f 1).re := by
  refine le_antisymm (f.toContinuousLinearMap.opNorm_le_bound
    (by simp [← norm_map_one]) f.norm_apply_le) ?_
  by_cases! Subsingleton A
  · simp [Subsingleton.eq_zero (1 : A)]
  simpa [norm_map_one] using f.toContinuousLinearMap.le_opNorm 1
