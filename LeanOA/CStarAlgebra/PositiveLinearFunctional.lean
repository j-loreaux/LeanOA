import LeanOA.Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import LeanOA.PositiveContinuousLinearMap
import LeanOA.Ultraweak.SeparatingDual
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

namespace PositiveContinuousLinearMap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_apply_le_sqrt_opNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ √‖(f : A →L[ℂ] ℂ)‖ * √‖f (star x * x)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine le_of_tendsto ((ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right _)).norm ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he1 he2
  grw [← he1.star_eq, Function.comp_apply, ← f.coe_toPositiveLinearMap,
    f.toPositiveLinearMap.cauchy_schwarz_star_mul, f.coe_toPositiveLinearMap,
    ← f.coe_toContinuousLinearMap, f.toContinuousLinearMap.le_opNorm (star e * e),
    CStarRing.norm_star_mul_self, he2, one_mul, mul_one]

open Topology in
theorem tendsto_isIncreasingApproximateUnit_nhds_opNorm (f : A →P[ℂ] ℂ) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) : l.Tendsto (‖f ·‖) (𝓝 ‖(f : A →L[ℂ] ℂ)‖) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have h : ∀ᶠ x in l, ‖f x‖ ≤ ‖(f : A →L[ℂ] ℂ)‖ + ε / 2 := by
    filter_upwards [hl.eventually_norm] with x hx
    grw [← f.coe_toContinuousLinearMap, ContinuousLinearMap.le_opNorm, hx, mul_one]
    grind
  have h2 : ∀ᶠ x in l, ‖(f : A →L[ℂ] ℂ)‖ - ε / 2 < ‖f x‖ := by
    obtain ⟨_, ⟨a, ha1, rfl⟩, ha2⟩ := exists_lt_of_lt_csSup (b := ‖(f : A →L[ℂ] ℂ)‖ - ε / 4)
      ((Metric.nonempty_closedBall (x := 0).mpr zero_le_one).image (‖f ·‖))
      (by grind [f.toContinuousLinearMap.sSup_unitClosedBall_eq_norm])
    have h3 : ∀ᶠ x in l, ‖f (x * a)‖ ^ 2 ≤ ‖f x‖ * ‖(f : A →L[ℂ] ℂ)‖ := by
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with x hx1 hx2
      have : ‖f (star x * x)‖ ≤ ‖f x‖ := by
        refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (star_mul_self_nonneg _)) ?_
        exact f.mono <| hx1.star_eq.symm ▸ CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hx1 hx2
      conv_lhs => rw [← hx1.star_eq, ← f.coe_toPositiveLinearMap]
      grw [f.cauchy_schwarz_star_mul x a, mul_pow, Real.sq_sqrt (norm_nonneg _),
        Real.sq_sqrt (norm_nonneg _), f.coe_toPositiveLinearMap, this,
        ← f.coe_toContinuousLinearMap, f.toContinuousLinearMap.le_opNorm (star a * a),
        CStarRing.norm_star_mul_self, ← mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      grw [mem_closedBall_zero_iff.mp ha1, one_mul]
    have h4 : ∀ᶠ x in l, ‖(f : A →L[ℂ] ℂ)‖ - ε / 4 < ‖f (x * a)‖ := by
      refine (Filter.Tendsto.norm ?_).eventually (lt_mem_nhds ha2)
      exact (ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right a)
    filter_upwards [h3, h4] with x _ _ using by nlinarith [norm_nonneg (f x)]
  filter_upwards [h, h2] using by grind [Real.dist_eq]

theorem opNorm_eq_norm_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →P[ℂ] ℂ) : ‖(f : A →L[ℂ] ℂ)‖ = ‖f 1‖ :=
  tendsto_nhds_unique (f.tendsto_isIncreasingApproximateUnit_nhds_opNorm (.pure_one A))
    (tendsto_pure_nhds _ _)

end PositiveContinuousLinearMap
