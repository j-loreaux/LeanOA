import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LeanOA.ForMathlib.Algebra.Star.Unitary
import LeanOA.ForMathlib.Misc

/-! # Properties of unitary elements in a C⋆-algebra

## Main results

+ `CStarAlgebra.exists_sum_four_unitary`: every element `x` in a unital C⋆-algebra is a linear
  combination of four unitary elements, and the norm of each coefficient does not exceed `‖x‖ / 2`.
+ `CStarAlgebra.span_unitary`: a unital C⋆-algebra is spanned by its unitary elements.

## To do

+ if `‖u - 1‖ < 1`, then there is a selfadjoint `x` such that `u = exp(I • x)`.
+ if `‖u - 1‖ < 1`, then there is a path of unitaries from `u` to `1`.
+ if `‖u - v‖ < 1`, then `u = exp(I • x) v`.
+ the path component of the identity in the unitary group is the set of unitaries `u` which
  are finite products of exponential unitaries.

-/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


section UnitarySpan

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
    -- I *really* want this to be solved with `cfc_pull`. This is a good example of a stress test.
    rw [cfc_add .., cfc_const_mul .., ← cfc_real_eq_complex (fun x ↦ x) ha, cfc_id' ℝ a,
      ← cfc_real_eq_complex (fun x ↦ √(1 - x ^2)) ha, cfcₙ_eq_cfc, cfc_comp' (√·) (1 - · ^ 2) a,
      cfc_sub .., cfc_pow .., cfc_const_one .., cfc_id' ..]
  rw [key, cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_ofReal_add_I_smul_sqrt_one_sub, Complex.ofReal_one]
  exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx) |>.trans ha_norm

@[simps]
noncomputable def selfAdjoint.unitarySelfAddISMul (a : selfAdjoint A)
    (ha_norm : ‖a‖ ≤ 1) :
    unitary A :=
  ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

lemma selfAdjoint.star_coe_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ ≤ 1) :
    (star (unitarySelfAddISMul a ha_norm) : A) = a - I • CFC.sqrt (1 - a ^ 2 : A) := by
  simp [a.2, IsSelfAdjoint.star_eq, ← sub_eq_add_neg,
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a := (1 - a ^ 2 : A)))]

@[simp high]
lemma selfAdjoint.realPart_unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ ≤ 1) :
    ℜ (unitarySelfAddISMul a ha_norm : A) = a := by
  simp [IsSelfAdjoint.imaginaryPart (x := CFC.sqrt (1 - a ^ 2 : A)) (by cfc_tac)]

/-- A stepping stone to `CStarAlgebra.exists_sum_four_unitary` that specifies the unitary
elements precisely. -/
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
  exact sum_mem fun i _ ↦ Submodule.smul_mem _ _ (subset_span (u i).2)



end UnitarySpan

section ExpUnitary

-- if `‖u - 1‖ < 1`, then there is a selfadjoint `x` such that `u = exp(I • x)`.

variable {A : Type*} [CStarAlgebra A]

open Complex


-- `Mathlib.Analysis.SpecialFunctions.Complex.Arg`
@[fun_prop]
theorem Complex.continuousOn_arg : ContinuousOn arg slitPlane :=
  fun _ h ↦ continuousAt_arg h |>.continuousWithinAt

@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (arg · : ℂ → ℂ) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star]

lemma spectrum_subset_slitPlane_of_norm_lt_one {u : A} (hu : ‖u - 1‖ < 1) :
    spectrum ℂ u ⊆ slitPlane := by
  nontriviality A
  have := spectrum.subset_closedBall_norm (𝕜 := ℂ) (u - 1) |>.trans <|
    Metric.closedBall_subset_ball hu
  rw [← map_one (algebraMap ℂ A), ← spectrum.sub_singleton_eq, Set.sub_singleton] at this
  exact fun x hx ↦ add_sub_cancel 1 x ▸ Complex.mem_slitPlane_of_norm_lt_one (by simpa using this ⟨x, hx, rfl⟩)


lemma unitary.expUnitary_cfc_arg_eq_of_norm_lt_one (u : unitary A) (hu : ‖(u - 1 : A)‖ < 1) :
    selfAdjoint.expUnitary ⟨cfc (arg · : ℂ → ℂ) (u : A), .cfc_arg (u : A)⟩ = u := by
  nontriviality A
  have h_cont : ContinuousOn (arg · : ℂ → ℂ) (spectrum ℂ (u : A)) :=
    continuous_ofReal.comp_continuousOn continuousOn_arg |>.mono <|
      spectrum_subset_slitPlane_of_norm_lt_one hu
  ext
  simp only [selfAdjoint.expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp, ← exp_eq_exp_ℂ, ← cfc_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun x hx ↦ ?_
  have hx₁ : ‖x‖ = 1 := by simpa using unitary.spectrum_subset_circle u hx
  convert Complex.exp_log (by simp [← norm_pos_iff, hx₁] : x ≠ 0) using 2
  apply Complex.ext
  all_goals simp [log_re, hx₁, log_im]

section

open Filter Topology

theorem ContinuousOn.tendsto_restrict_iff_tendstoUniformlyOn {α β : Type*}
    [TopologicalSpace α] [UniformSpace β] {s : Set α} [CompactSpace s]
    {f : α → β} (hf : ContinuousOn f s) {ι : Type*} {p : Filter ι}
    {F : ι → α → β} (hF : ∀ i, ContinuousOn (F i) s) :
    Tendsto (fun i ↦ ⟨_, (hF i).restrict⟩ : ι → C(s, β)) p (𝓝 ⟨_, hf.restrict⟩) ↔
      TendstoUniformlyOn F f p s := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  congr!

theorem continuousAt_cfc (a : A) [ha : IsStarNormal a] {X : Type*} [TopologicalSpace X]
    {f : X → ℂ → ℂ} (hf : ∀ x, ContinuousOn (f x) (spectrum ℂ a)) (x₀ : X)
    (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum ℂ a)) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ := by
  conv =>
    enter [1, x]
    rw [cfc_apply ..]
  apply cfcHom_continuous ha |>.continuousAt.comp
  rwa [ContinuousAt, (hf x₀).tendsto_restrict_iff_tendstoUniformlyOn hf]

end


--- we need the other lemmas like this
open UniformFun in
theorem ContinuousMap.continuous_iff_continuous_uniformFun {X α β : Type*}
    [TopologicalSpace X] [TopologicalSpace α] [UniformSpace β] (f : X → C(α, β)) [CompactSpace α] :
    Continuous f ↔ Continuous (fun x ↦ ofFun (f x)) := by
  simp only [continuous_iff_continuousAt]
  apply forall_congr' fun x ↦ ?_
  simp [ContinuousAt, tendsto_iff_tendstoUniformly, UniformFun.tendsto_iff_tendstoUniformly,
    Function.comp_def]

attribute [fun_prop] NormedSpace.exp_continuous

open Real in
noncomputable
def unitary.pathToOne (u : unitary A) (hu : ‖(u - 1 : A)‖ < 1) : Path 1 u where
  toFun t := selfAdjoint.expUnitary
    ⟨cfc (t * arg · : ℂ → ℂ) (u : A), by simp [selfAdjoint.mem_iff, ← cfc_star]⟩
  continuous_toFun := by
    simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
    suffices Continuous fun x : unitInterval ↦ cfc (fun z ↦ x * arg z) (u : A) by fun_prop
    rw [continuous_iff_continuousAt]
    intro x₀
    apply continuousAt_cfc
    · exact fun _ ↦ ContinuousOn.mono (by fun_prop) (spectrum_subset_slitPlane_of_norm_lt_one hu)
    · rw [Metric.tendstoUniformlyOn_iff]
      simp [dist_eq_norm, ← sub_mul]
      intro ε hε
      filter_upwards [Metric.ball_mem_nhds x₀ (ε := ε / π) (by positivity)] with x hx z hz
      calc
        ‖(x₀ - x : ℂ)‖ * |z.arg| ≤ ‖(x₀ - x : ℂ)‖ * π := by gcongr; exact Complex.abs_arg_le_pi z
        _ < ε / π * π := by
          gcongr
          simpa [Subtype.dist_eq, dist_eq_norm, ← Complex.ofReal_sub, abs_sub_comm] using hx
        _ = ε := div_mul_cancel₀ _ (by positivity)
  source' := by ext; simp
  target' := by
    ext
    simpa using congr(Subtype.val $(unitary.expUnitary_cfc_arg_eq_of_norm_lt_one u hu))


end ExpUnitary
