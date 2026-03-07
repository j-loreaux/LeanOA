import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import LeanOA.PositiveContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

open scoped ComplexOrder

namespace PositiveLinearMap
section CauchySchwarz

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

-- we need to generalize GNS to this setting in order to get the Cauchy-Schwarz inequality
-- for positive linear functionals on type synonyms of C⋆-algebras.
variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [Module ℂ A] (f : A →ₚ[ℂ] ℂ)

set_option linter.unusedVariables false in
/-- The Gelfand─Naimark─Segal (GNS) space constructed from a positive linear functional on a
non-unital C⋆-algebra. This is a type synonym of `A`.

This space is only a pre-inner product space. Its Hilbert space completion is
`PositiveLinearMap.GNS`. -/
@[nolint unusedArguments]
def PreGNS' (f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup f.PreGNS' := inferInstanceAs (AddCommGroup A)
instance : Module ℂ f.PreGNS' := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toPreGNS' : A ≃ₗ[ℂ] f.PreGNS' := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofPreGNS' : f.PreGNS' ≃ₗ[ℂ] A := f.toPreGNS'.symm

@[simp]
lemma toPreGNS'_ofPreGNS' (a : f.PreGNS') : f.toPreGNS' (f.ofPreGNS' a) = a := rfl

@[simp]
lemma ofPreGNS'_toPreGNS' (a : A) : f.ofPreGNS' (f.toPreGNS' a) = a := rfl

variable [StarRing A] [StarOrderedRing A] [SelfAdjointDecompose A] [StarModule ℂ A]
    [IsScalarTower ℂ A A]

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm that is different from the norm on `A` and which is induced by `f`.
-/
noncomputable abbrev preGNS'preInnerProdSpace : PreInnerProductSpace.Core ℂ f.PreGNS' where
  inner a b := f (star (f.ofPreGNS' a) * f.ofPreGNS' b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

noncomputable instance : SeminormedAddCommGroup f.PreGNS' :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNS'preInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.PreGNS' :=
  InnerProductSpace.ofCore f.preGNS'preInnerProdSpace

lemma preGNS'_inner_def (a b : f.PreGNS') :
    ⟪a, b⟫_ℂ = f (star (f.ofPreGNS' a) * f.ofPreGNS' b) := rfl

lemma preGNS'_norm_def (a : f.PreGNS') :
    ‖a‖ = √(f (star (f.ofPreGNS' a) * f.ofPreGNS' a)).re := rfl

lemma preGNS'_norm_sq (a : f.PreGNS') :
    ‖a‖ ^ 2 = f (star (f.ofPreGNS' a) * f.ofPreGNS' a) := by
  have : 0 ≤ f (star (f.ofPreGNS' a) * f.ofPreGNS' a) := map_nonneg f <| star_mul_self_nonneg _
  rw [preGNS'_norm_def, ← ofReal_pow, Real.sq_sqrt]
  · rw [conj_eq_iff_re.mp this.star_eq]
  · rwa [re_nonneg_iff_nonneg this.isSelfAdjoint]

lemma preGNS'_norm_def' (f : A →ₚ[ℂ] ℂ) (a : f.PreGNS') :
    ‖a‖ = √‖f (star (f.ofPreGNS' a) * f.ofPreGNS' a)‖ := by
  rw [← sq_eq_sq₀ (by positivity) (by positivity), ← Complex.ofReal_inj,
    Complex.ofReal_pow, preGNS'_norm_sq, Real.sq_sqrt (by positivity),
    ← Complex.eq_coe_norm_of_nonneg]
  exact map_nonneg f (star_mul_self_nonneg _)

lemma cauchy_schwarz_star_mul (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (star x * y)‖ ≤ √‖f (star x * x)‖ * √‖f (star y * y)‖ := by
  simpa [preGNS'_inner_def, preGNS'_norm_def'] using
    norm_inner_le_norm (f.toPreGNS' x) (f.toPreGNS' y)

lemma cauchy_schwarz_mul_star (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (x * star y)‖ ≤ √‖f (x * star x)‖ * √‖f (y * star y)‖ := by
  simpa using cauchy_schwarz_star_mul f (star x) (star y)

end CauchySchwarz

end PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

set_option backward.isDefEq.respectTransparency false in
lemma PositiveLinearMap.norm_apply_le (f : A →ₚ[ℂ] ℂ) (x : A) : ‖f x‖ ≤ (f 1).re * ‖x‖ := by
  have := by simpa [f.preGNS_norm_def, f.preGNS_inner_def] using
    norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS 1) (f.toPreGNS x)
  have hf := Complex.nonneg_iff.mp (f.map_nonneg zero_le_one) |>.1
  grw [this, ← sq_le_sq₀ (by positivity) (mul_nonneg hf (by positivity))]
  simp_rw [mul_pow, Real.sq_sqrt hf, sq, mul_assoc, ← sq, Real.sq_sqrt
    (Complex.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _))).1]
  refine mul_le_mul_of_nonneg_left ?_ hf
  have := by simpa [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one, ← sq] using
    f.apply_le_of_isSelfAdjoint _ (.star_mul_self x)
  convert Complex.le_def.mp this |>.1
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, mul_comm]

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
