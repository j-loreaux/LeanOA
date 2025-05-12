
import LeanOA.ContinuousFunctionalCalculus.Continuity
import LeanOA.ForMathlib.Algebra.Star.Unitary
import LeanOA.ForMathlib.Analysis.CStarAlgebra.Basic
import LeanOA.ForMathlib.Analysis.CStarAlgebra.Exponential
import LeanOA.ForMathlib.Analysis.CStarAlgebra.Spectrum
import LeanOA.ForMathlib.Analysis.Complex.Basic
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LeanOA.ForMathlib.Data.Complex.Norm
import LeanOA.ForMathlib.Data.Complex.Order
import LeanOA.ForMathlib.Misc
import LeanOA.ForMathlib.Topology.Algebra.Star.Unitary
import LeanOA.ForMathlib.Topology.Connected.PathConnected
import LeanOA.ForMathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-! # Properties of unitary elements in a C⋆-algebra

## Main results

+ `CStarAlgebra.exists_sum_four_unitary`: every element `x` in a unital C⋆-algebra is a linear
  combination of four unitary elements, and the norm of each coefficient does not exceed `‖x‖ / 2`.
+ `CStarAlgebra.span_unitary`: a unital C⋆-algebra is spanned by its unitary elements.
-/

variable {A : Type*} [CStarAlgebra A]

section UnitarySpan

variable [PartialOrder A] [StarOrderedRing A]
open scoped ComplexStarModule
open Complex

/-- If `a : A` is a selfadjoint element in a C⋆-algebra with `‖a‖ ≤ 1`,
then `a + I • CFC.sqrt (1 - a ^ 2)` is unitary.

This is the key tool to show that a C⋆-algebra is spanned by its unitary elements. -/
lemma IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary (a : A) (ha : IsSelfAdjoint a)
    (ha_norm : ‖a‖ ≤ 1) : a + I • CFC.sqrt (1 - a ^ 2) ∈ unitary A := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1]
  have key : a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x : ℂ ↦ x.re + I * √(1 - x.re ^ 2)) a := by
    rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
    case nonneg =>
      rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), ha.sq_norm,
        sq_le_one_iff₀ (by positivity)]
    -- I *really* want this to be solved with a `cfc_pull` tactic. This is a good example of a stress test.
    rw [cfc_add .., cfc_const_mul .., ← cfc_real_eq_complex (fun x ↦ x) ha, cfc_id' ℝ a,
      ← cfc_real_eq_complex (fun x ↦ √(1 - x ^2)) ha, cfcₙ_eq_cfc, cfc_comp' (√·) (1 - · ^ 2) a,
      cfc_sub .., cfc_pow .., cfc_const_one .., cfc_id' ..]
  rw [key, cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_ofReal_add_I_smul_sqrt_one_sub, Complex.ofReal_one]
  exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx) |>.trans ha_norm

/-- For `a` selfadjoint with `‖a‖ ≤ 1`, this is the unitary `a + I • √(1 - a ^ 2)`. -/
@[simps]
noncomputable def selfAdjoint.unitarySelfAddISMul (a : selfAdjoint A)
    (ha_norm : ‖a‖ ≤ 1) :
    unitary A :=
  ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

lemma selfAdjoint.star_coe_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ ≤ 1) :
    (star (unitarySelfAddISMul a ha_norm) : A) = a - I • CFC.sqrt (1 - a ^ 2 : A) := by
  simp [a.2, IsSelfAdjoint.star_eq, ← sub_eq_add_neg,
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a := (1 - a ^ 2 : A)))]

lemma selfAdjoint.realPart_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ ≤ 1) :
    ℜ (unitarySelfAddISMul a ha_norm : A) = a := by
  simp [IsSelfAdjoint.imaginaryPart (x := CFC.sqrt (1 - a ^ 2 : A)) (by cfc_tac)]

/-- A stepping stone to `CStarAlgebra.exists_sum_four_unitary` that specifies the unitary
elements precisely. The `let`s in the statement are intentional. -/
lemma CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary (x : A) (hx : x ≠ 0) :
    let u₁ : unitary A := selfAdjoint.unitarySelfAddISMul (ℜ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using realPart.norm_le x)
    let u₂ : unitary A := selfAdjoint.unitarySelfAddISMul (ℑ (‖x‖⁻¹ • x))
      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using imaginaryPart.norm_le x)
    x = ‖x‖ • (2⁻¹ : ℝ) • (u₁ + star u₁ + I • (u₂ + star u₂) : A) := by
  intro u₁ u₂
  rw [smul_add, smul_comm _ I, unitary.coe_star, unitary.coe_star,
    ← realPart_apply_coe (u₁ : A), ← realPart_apply_coe (u₂ : A)]
  simp only [u₁, u₂, selfAdjoint.realPart_unitarySelfAddISMul,
    realPart_add_I_smul_imaginaryPart, norm_smul_norm_inv_smul]

/-- Every element `x` in a unital C⋆-algebra is a linear combination of four unitary elements,
and the norm of each coefficient does not exceed `‖x‖ / 2`. -/
lemma CStarAlgebra.exists_sum_four_unitary (x : A) :
    ∃ u : Fin 4 → unitary A, ∃ c : Fin 4 → ℂ, x = ∑ i, c i • (u i : A) ∧ ∀ i, ‖c i‖ ≤ ‖x‖ / 2 := by
  obtain (rfl | hx) := eq_or_ne x 0
  · exact ⟨![1, -1, 1, -1], 0, by simp⟩
  · have := norm_smul_two_inv_smul_add_four_unitary x hx
    extract_lets u₁ u₂ at this
    use ![u₁, star u₁, u₂, star u₂]
    use ![‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹, ‖x‖ * 2⁻¹ * I, ‖x‖ * 2⁻¹ * I]
    constructor
    · conv_lhs => rw [this]
      simp [Fin.sum_univ_four, ← Complex.coe_smul]
      module
    · intro i
      fin_cases i
      all_goals simp [div_eq_mul_inv]

variable (A) in
open Submodule in
/-- A unital C⋆-algebra is spanned by its unitary elements. -/
lemma CStarAlgebra.span_unitary : span ℂ (unitary A : Set A) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨u, c, rfl, h⟩ := CStarAlgebra.exists_sum_four_unitary x
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (u i).2)

end UnitarySpan
