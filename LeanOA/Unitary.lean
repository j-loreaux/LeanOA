import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import LeanOA.ForMathlib.Algebra.Star.Unitary
import LeanOA.ForMathlib.Misc
import LeanOA.ContinuousMap.Uniform
import LeanOA.ContinuousFunctionalCalculus.Continuity
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

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
+ `unitary A` is locally path connected

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


@[aesop safe apply (rule_sets := [CStarAlgebra])] -- this has a bad discr tree key :-(
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (arg · : ℂ → ℂ) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star]

attribute [fun_prop] NormedSpace.exp_continuous


lemma Complex.norm_sub_one_sq_eq_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm, normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring

open Metric in
lemma Complex.norm_sub_one_sq_eqOn_sphere :
    (sphere (0 : ℂ) 1).EqOn (‖· - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
  fun z hz ↦ norm_sub_one_sq_eq_of_norm_one (by simpa using hz)

attribute [aesop 10% apply (rule_sets := [CStarAlgebra])] isStarNormal_of_mem_unitary

open Complex in
lemma unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u ∈ unitary A)
    {z : ℂ} (hz : z ∈ spectrum ℂ u) :
    2 * (1 - z.re) ≤ ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  convert norm_apply_le_norm_cfc (fun z ↦ z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_one this)).symm

open Complex in
lemma unitary.norm_sub_one_sq_eq {u : A} (hu : u ∈ unitary A) {x : ℝ}
    (hz : IsLeast (re '' (spectrum ℂ u)) x) :
    ‖u - 1‖ ^ 2 = 2 * (1 - x) := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  have h_eqOn : (spectrum ℂ u).EqOn (fun z ↦ ‖z - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
    Complex.norm_sub_one_sq_eqOn_sphere.mono <| spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu
  have h₂ : IsGreatest ((fun z ↦ 2 * (1 - z.re)) '' (spectrum ℂ u)) (2 * (1 - x)) := by
    have : Antitone (fun y : ℝ ↦ 2 * (1 - y)) := by intro _ _ _; simp only; gcongr
    simpa [Set.image_image] using this.map_isLeast hz
  have h₃ : IsGreatest ((‖· - 1‖ ^ 2) '' spectrum ℂ u) (‖cfc (· - 1 : ℂ → ℂ) u‖ ^ 2) := by
    have := pow_left_monotoneOn (n := 2) |>.mono (s₂ := ((‖· - 1‖) '' spectrum ℂ u)) (by aesop)
    simpa [Set.image_image] using this.map_isGreatest (IsGreatest.norm_cfc (fun z : ℂ ↦ z - 1) u)
  exact h₃.unique (h_eqOn.image_eq ▸ h₂)

-- move to `Analysis.CStarAlgebra.Spectrum`
theorem spectrum.norm_eq_one_of_unitary {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E]
    [StarRing E] [CStarRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] {u : E} (hu : u ∈ unitary E)
    ⦃z : 𝕜⦄ (hz : z ∈ spectrum 𝕜 u) : ‖z‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary hu hz

lemma Complex.norm_le_re_iff_eq_norm {z : ℂ} :
    ‖z‖ ≤ z.re ↔ z = ‖z‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · replace h : z.re = ‖z‖ := le_antisymm (re_le_norm z) h
    apply ext
    · simp [h]
    · rw [re_eq_norm, nonneg_iff] at h
      simpa using h.2.symm
  · rw [h]
    simp

lemma Complex.re_le_neg_norm_iff_eq_neg_norm {z : ℂ} :
    z.re ≤ -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

lemma Complex.norm_le_im_iff_eq_I_mul_norm {z : ℂ} :
    ‖z‖ ≤ z.im ↔ z = I * ‖z‖ := by
  have := norm_le_re_iff_eq_norm (z := -I * z)
  simp only [Complex.norm_mul, norm_neg, norm_I, one_mul, mul_re, neg_re, I_re,
    neg_zero, zero_mul, neg_im, I_im, zero_sub, ← neg_mul, neg_neg] at this
  rw [this, ← smul_eq_mul, eq_comm, ← inv_smul_eq_iff₀ (by simp)]
  simp [← neg_inv, eq_comm]

lemma Complex.im_le_neg_norm_iff_eq_neg_I_mul_norm {z : ℂ} :
    z.im ≤ -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

lemma unitary.norm_sub_one_lt_two_iff {u : A} (hu : u ∈ unitary A) :
    ‖u - 1‖ < 2 ↔ -1 ∉ spectrum ℂ u := by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
    have := unitary.two_mul_one_sub_le_norm_sub_one_sq hu h1 |>.trans_lt h
    norm_num at this
  · contrapose!
    obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := ℂ) u |>.image continuous_re |>.exists_isLeast <| (spectrum.nonempty _).image _
    rw [unitary.norm_sub_one_sq_eq hu hx]
    obtain ⟨z, hz, rfl⟩ := hx.1
    intro key
    replace key : z.re ≤ -1 := by linarith
    have hz_norm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
    rw [← hz_norm, Complex.re_le_neg_norm_iff_eq_neg_norm, hz_norm] at key
    exact key ▸ hz

lemma unitary.spectrum_subset_slitPlane_of_norm_lt_two {u : A} (hu : u ∈ unitary A)
    (hu_norm : ‖u - 1‖ < 2) :
    spectrum ℂ u ⊆ slitPlane:= by
  intro z hz
  rw [mem_slitPlane_iff]
  have hz_norm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
  have := sq_eq_one_iff.mpr <| .inl hz_norm
  rw [← normSq_eq_norm_sq, normSq_apply] at this
  by_cases h : z.im = 0
  · simp [h, ← sq] at this
    cases this with
    | inl h => simp [h]
    | inr h =>
      have := hz_norm ▸ h.le
      rw [Complex.re_le_neg_norm_iff_eq_neg_norm, hz_norm, ofReal_one] at this
      rw [unitary.norm_sub_one_lt_two_iff hu] at hu_norm
      exact False.elim <| hu_norm (this ▸ hz)
  · exact .inr h

/-- The selfadjoint element obtained by taking the argument (using the principal branch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum of the unitary
element. -/
@[simps]
noncomputable def unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A :=
  ⟨cfc (arg · : ℂ → ℂ) (u : A), .cfc_arg (u : A)⟩

open scoped Real in
lemma selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ ≤ π) :
    ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) := by
  nontriviality A
  apply unitary.norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe, AddSubgroupClass.coe_norm]
  rw [← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul I _ (x : A), cfc_map_spectrum .., ← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ, exp_ofReal_mul_I_re]
  refine ⟨?_, ?_⟩
  · cases CStarAlgebra.norm_or_neg_norm_mem_spectrum x.2 with
    | inl h => exact ⟨_, h, rfl⟩
    | inr h => exact ⟨_, h, by simp⟩
  · rintro - ⟨y, hy, rfl⟩
    exact Real.cos_abs y ▸ Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx <| spectrum.norm_le_norm_of_mem hy

open scoped Real in
open unitary selfAdjoint in
lemma argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) :
    argSelfAdjoint (expUnitary x) = x := by
  nontriviality A
  ext
  have : spectrum ℂ (expUnitary x : A) ⊆ slitPlane := by
    apply unitary.spectrum_subset_slitPlane_of_norm_lt_two (expUnitary x).2
    rw [← sq_lt_sq₀ (by positivity) (by positivity), norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1 - Real.cos π) := by
        gcongr
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
      _ = 2 ^ 2 := by norm_num
  simp only [argSelfAdjoint_coe, expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul .., ← cfc_comp' (hg := ?_)]
  · conv_rhs => rw [← cfc_id' ℂ (x : A)]
    refine cfc_congr fun y hy ↦ ?_
    rw [← x.2.spectrumRestricts.algebraMap_image] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    simp [← exp_eq_exp_ℂ, exp_ofReal_mul_I_re, mul_comm I, ← ofReal_mul, exp_ofReal_mul_I_re]
    replace hy : ‖y‖ < π := spectrum.norm_le_norm_of_mem hy |>.trans_lt hx
    simp only [Real.norm_eq_abs, abs_lt] at hy
    rw [← Circle.coe_exp, Circle.arg_exp hy.1 hy.2.le]
  refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
  rwa [expUnitary_coe, ← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul .., cfc_map_spectrum ..] at this

open scoped Real in
open unitary selfAdjoint in
lemma expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) :=
    continuousOn_arg.mono <| unitary.spectrum_subset_slitPlane_of_norm_lt_two u.2 hu
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

-- this can be generalized
@[simp]
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

open scoped Real in
lemma unitary.norm_argSelfAdjoint_le_pi (u : unitary A) :
    ‖argSelfAdjoint u‖ ≤ π :=
  norm_cfc_le (by positivity) fun y hy ↦ by simpa using abs_arg_le_pi y

lemma unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(u - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖argSelfAdjoint u‖) := by
  conv_lhs => rw [← expUnitary_argSelfAdjoint hu]
  exact selfAdjoint.norm_sq_expUnitary_sub_one <| unitary.norm_argSelfAdjoint_le_pi u

lemma unitary.norm_argSelfAdjoint' {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) := by
  symm
  apply Real.arccos_eq_of_eq_cos (by positivity) (unitary.norm_argSelfAdjoint_le_pi u)
  linarith [unitary.norm_argSelfAdjoint hu]

open scoped Real in
open NormedSpace Complex unitary selfAdjoint in
lemma unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(expUnitary (t • argSelfAdjoint u) - 1 : A)‖ ≤ ‖(u - 1 : A)‖ := by
  have key : ‖t • argSelfAdjoint u‖ ≤ ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [selfAdjoint.norm_sq_expUnitary_sub_one (key.trans <| unitary.norm_argSelfAdjoint_le_pi u)]
  trans 2 * (1 - Real.cos ‖argSelfAdjoint u‖)
  · gcongr
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (unitary.norm_argSelfAdjoint_le_pi u) key
  · exact (unitary.norm_argSelfAdjoint hu).ge

lemma Metric.nhds_basis_ball_lt {X : Type*} [PseudoMetricSpace X] (x : X) (δ : ℝ) (hδ : 0 < δ) :
    (nhds x).HasBasis (fun ε ↦ 0 < ε ∧ ε < δ) (ball x ·) := by
  refine nhds_basis_ball.restrict fun ε hε ↦
    ⟨min δ ε / 2, by positivity, ?_, ball_subset_ball (le_of_lt ?_)⟩
  all_goals
    apply (half_lt_self (by positivity)).trans_le
    simp

lemma unitary.norm_sub_eq (u v : unitary A) :
    ‖(u - v : A)‖ = ‖((u * star v : unitary A) - 1 : A)‖ := calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp

open selfAdjoint unitary in
lemma unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) :
    expUnitary (argSelfAdjoint (u * star v)) = u * star v :=
  expUnitary_argSelfAdjoint <| unitary.norm_sub_eq u v ▸ huv

open scoped Real in
open selfAdjoint Metric in
/-- the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`. -/
noncomputable def unitary.partialHomeomorph :
    PartialHomeomorph (unitary A) (selfAdjoint A) where
  toFun := argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' := sorry
  map_target' := sorry
  left_inv' u hu := expUnitary_argSelfAdjoint <| by
    simpa [Subtype.dist_eq, dist_eq_norm] using hu
  right_inv' x hx := argSelfAdjoint_expUnitary <| by simpa using hx
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

open Real selfAdjoint unitary in
@[simps]
noncomputable
def unitary.pathToOne (u : unitary A) (hu : ‖(u - 1 : A)‖ < 2) : Path 1 u where
  toFun t := expUnitary ((t : ℝ) • argSelfAdjoint u)
  continuous_toFun := by
    simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
    suffices Continuous fun x : unitInterval ↦ cfc (fun z ↦ x * arg z) (u : A) by fun_prop
    obtain (h | h) := subsingleton_or_nontrivial A
    · convert continuous_const (y := (0 : A))
    refine continuous_cfc_right (hf := ?hf_cont) _ (u : A) ?h_cont
    case hf_cont => exact fun _ ↦ ContinuousOn.mono (by fun_prop) (unitary.spectrum_subset_slitPlane_of_norm_lt_two u.2 hu)
    case h_cont =>
      apply UniformOnFun.continuous_of_lipschitzWith (fun _ : Set ℂ ↦ ⟨π, by positivity⟩)
      simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq,
        lipschitzWith_iff_dist_le_mul, dist_eq_norm, Subtype.dist_eq, ← sub_mul,
        ← Complex.ofReal_sub, norm_mul, Complex.norm_real]
      rintro _ - _ _
      rw [mul_comm]
      gcongr
      exact Complex.abs_arg_le_pi _
  source' := by ext; simp
  target' := by simpa using expUnitary_argSelfAdjoint hu

variable (A) in
open Metric in
lemma unitary.ball_one_isPathConnected (δ : ℝ) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (1 : unitary A) δ) := by
  refine ⟨1, by simpa, fun {u} hu ↦ ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [Subtype.dist_eq, dist_eq_norm] using hu
  refine ⟨pathToOne u (hu.trans hδ₂), fun t ↦ ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm] using
    unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le u t.2 (hu.trans hδ₂) |>.trans_lt hu

open Metric in
lemma unitary.ball_isPathConnected (u : unitary A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (u : unitary A) δ) := by
  convert unitary.ball_one_isPathConnected A δ hδ₀ hδ₂ |>.image (f := (u * ·)) (by fun_prop)
  ext v
  rw [← inv_mul_cancel u]
  simp [- inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]

open Metric in
instance : LocPathConnectedSpace (unitary A) :=
  .of_bases (nhds_basis_ball_lt · 2 zero_lt_two) <| by
    simpa using unitary.ball_isPathConnected

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G]

@[to_additive]
theorem Joined.mul {x y w z : G} [Mul G] [ContinuousMul G] (hxy : Joined x y) (hwz : Joined w z) :
    Joined (x * w) (y * z) := by
  obtain ⟨γ₁⟩ := hxy
  obtain ⟨γ₂⟩ := hwz
  use γ₁.mul γ₂
  all_goals simp

/-- The pointwise inverse of a path. -/
@[to_additive (attr := simps) "The pointwise negation of a path."]
def Path.inv {x y : G} [Inv G] [ContinuousInv G] (γ : Path x y) :
    Path (x⁻¹) (y⁻¹) where
  toFun := γ⁻¹
  continuous_toFun := map_continuous γ |>.inv
  source' := congr($(γ.source)⁻¹)
  target' := congr($(γ.target)⁻¹)

@[to_additive]
theorem Joined.inv {x y : G} [Inv G] [ContinuousInv G] (hxy : Joined x y) :
    Joined (x⁻¹) (y⁻¹) := by
  obtain ⟨γ⟩ := hxy
  use γ.inv
  all_goals simp

variable (G)
/-- The path component of the identity in a topological monoid, as a submonoid. -/
@[to_additive (attr := simps)
"The path component of the identity in an additive topological monoid, as an additive submonoid."]
def Submonoid.pathComponentOne [Monoid G] [ContinuousMul G] : Submonoid G where
  carrier := pathComponent (1 : G)
  mul_mem' {g₁ g₂} hg₁ hg₂ := by simpa using hg₁.mul hg₂
  one_mem' := mem_pathComponent_self 1

/-- The path component of the identity in a topological group, as a subgroup. -/
@[to_additive (attr := simps!)
"The path component of the identity in an additive topological group, as an additive subgroup."]
def Subgroup.pathComponentOne [Group G] [IsTopologicalGroup G] : Subgroup G where
  toSubmonoid := .pathComponentOne G
  inv_mem' {g} hg := by simpa using hg.inv

/-- The path component of the identity in a topological group is normal-/
@[to_additive]
instance Subgroup.Normal.pathComponentOne [Group G] [IsTopologicalGroup G] :
    (Subgroup.pathComponentOne G).Normal where
  conj_mem _ := fun ⟨γ⟩ g ↦ ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

/-- The path component of the identity in a locally path connected topological group,
as an open normal subgroup. -/
@[to_additive (attr := simps!)
"The path component of the identity in a locally path connected additive topological group,
as an open normal additive subgroup."]
def OpenNormalSubgroup.pathComponentOne [Group G]
    [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    OpenNormalSubgroup (G) where
  toSubgroup := .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

namespace OpenNormalSubgroup

@[to_additive]
instance [Group G] [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    IsClosed (OpenNormalSubgroup.pathComponentOne G : Set G) :=
  .pathComponent 1

end OpenNormalSubgroup

end TopologicalGroup

-- these instances can be generalized a bit, at least to `CStarRing`
instance {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
    ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr <| by fun_prop

instance {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] :
    ContinuousInv (unitary R) where
  continuous_inv := by simp_rw [← unitary.star_eq_inv]; fun_prop

instance : IsTopologicalGroup (unitary A) where

end ExpUnitary
