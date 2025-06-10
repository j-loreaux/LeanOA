import LeanOA.ForMathlib.Analysis.CStarAlgebra.Basic
import LeanOA.ForMathlib.Analysis.CStarAlgebra.Spectrum
import LeanOA.ForMathlib.Analysis.Complex.Basic
import LeanOA.ForMathlib.Data.Complex.Norm
import LeanOA.ForMathlib.Data.Complex.Order
import LeanOA.ForMathlib.Misc
import LeanOA.ForMathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-! # Properties of unitary elements in a C⋆-algebra

## Main results

+ `CStarAlgebra.exists_sum_four_unitary`: every element `x` in a unital C⋆-algebra is a linear
  combination of four unitary elements, and the norm of each coefficient does not exceed `‖x‖ / 2`.
+ `CStarAlgebra.span_unitary`: a unital C⋆-algebra is spanned by its unitary elements.
+ `unitary.argSelfAdjoint`: the selfadjoint element obtained by taking the argument (using the
  principal branch and the continuous functional calculus) of a unitary. This returns `0` if
  the principal branch of the logarithm is not continuous on the spectrum of the unitary element.
+ `selfAdjoint.norm_sq_expUnitary_sub_one`:
  `‖(selfAdjoint.expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)`
+ `unitary.norm_argSelfAdjoint`:
  `‖unitary.argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)`
+ `unitary.partialHomeomorph`: the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form
  a partial homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
+ `selfAdjoint.expUnitary_pathToOne`: the path `t ↦ expUnitary (t • x)` from `1` to
  `expUnitary x` for a selfadjoint element `x`.
+ `unitary.isPathConnected_ball`: any ball of radius `δ < 2` in the unitary group of a unital
  C⋆-algebra is path connected.
+ `unitary.instLocPathConnectedSpace`: the unitary group of a C⋆-algebra is locally path connected.
+ `unitary.mem_pathComponentOne_iff`: The path component of the identity in the unitary group of a
  C⋆-algebra is the set of unitaries that can be expressed as a product of exponentials of
  selfadjoint elements.
-/

variable {A : Type*} [CStarAlgebra A]

section UnitarySpan

open scoped ComplexStarModule
open Complex

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- If `a : A` is a selfadjoint element in a C⋆-algebra with `‖a‖ ≤ 1`,
then `a + I • CFC.sqrt (1 - a ^ 2)` is unitary.

This is the key tool to show that a C⋆-algebra is spanned by its unitary elements. -/
lemma IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary (a : A) (ha : IsSelfAdjoint a)
    (ha_norm : ‖a‖ ≤ 1) : a + I • CFC.sqrt (1 - a ^ 2) ∈ unitary A := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1, one_mem (unitary A)]
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

end Ordered

/-- Every element `x` in a unital C⋆-algebra is a linear combination of four unitary elements,
and the norm of each coefficient does not exceed `‖x‖ / 2`. -/
lemma CStarAlgebra.exists_sum_four_unitary (x : A) :
    ∃ u : Fin 4 → unitary A, ∃ c : Fin 4 → ℂ, x = ∑ i, c i • (u i : A) ∧ ∀ i, ‖c i‖ ≤ ‖x‖ / 2 := by
  let _ := CStarAlgebra.spectralOrder
  let _ := CStarAlgebra.spectralOrderedRing
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

section ExpUnitary

variable {A : Type*} [CStarAlgebra A]

open Complex Metric NormedSpace selfAdjoint unitary
open scoped Real

lemma unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u ∈ unitary A)
    {z : ℂ} (hz : z ∈ spectrum ℂ u) :
    2 * (1 - z.re) ≤ ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  convert norm_apply_le_norm_cfc (fun z ↦ z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_one this)).symm

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

lemma unitary.norm_sub_one_lt_two_iff {u : A} (hu : u ∈ unitary A) :
    ‖u - 1‖ < 2 ↔ -1 ∉ spectrum ℂ u := by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
    have := two_mul_one_sub_le_norm_sub_one_sq hu h1 |>.trans_lt h
    norm_num at this
  · contrapose!
    obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := ℂ) u |>.image continuous_re |>.exists_isLeast <| (spectrum.nonempty _).image _
    rw [norm_sub_one_sq_eq hu hx]
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
      rw [norm_sub_one_lt_two_iff hu] at hu_norm
      exact False.elim <| hu_norm (this ▸ hz)
  · exact .inr h

@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (ofReal ∘ arg : ℂ → ℂ) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

/-- The selfadjoint element obtained by taking the argument (using the principal branch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum of the unitary
element. -/
@[simps]
noncomputable def unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A :=
  ⟨cfc (arg · : ℂ → ℂ) (u : A), .cfc_arg (u : A)⟩

lemma selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ ≤ π) :
    ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) := by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe, AddSubgroupClass.coe_norm]
  rw [← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul I _ (x : A), cfc_map_spectrum .., ← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ, exp_ofReal_mul_I_re]
  refine ⟨?_, ?_⟩
  · cases CStarAlgebra.norm_or_neg_norm_mem_spectrum x.2 with
    | inl h => exact ⟨_, h, rfl⟩
    | inr h => exact ⟨_, h, by simp⟩
  · rintro - ⟨y, hy, rfl⟩
    exact Real.cos_abs y ▸ Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx <| spectrum.norm_le_norm_of_mem hy

lemma argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) :
    argSelfAdjoint (expUnitary x) = x := by
  nontriviality A
  ext
  have : spectrum ℂ (expUnitary x : A) ⊆ slitPlane := by
    apply spectrum_subset_slitPlane_of_norm_lt_two (expUnitary x).2
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

lemma expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) :=
    continuousOn_arg.mono <| spectrum_subset_slitPlane_of_norm_lt_two u.2 hu
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp, ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

lemma unitary.norm_argSelfAdjoint_le_pi (u : unitary A) :
    ‖argSelfAdjoint u‖ ≤ π :=
  norm_cfc_le (by positivity) fun y hy ↦ by simpa using abs_arg_le_pi y

lemma unitary.two_mul_one_sub_cos_norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    2 * (1 - Real.cos ‖argSelfAdjoint u‖) = ‖(u - 1 : A)‖ ^ 2 := by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
  exact Eq.symm <| norm_sq_expUnitary_sub_one <| norm_argSelfAdjoint_le_pi u

lemma unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) := by
  refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_ |>.symm
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

lemma unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(expUnitary (t • argSelfAdjoint u) - 1 : A)‖ ≤ ‖(u - 1 : A)‖ := by
  have key : ‖t • argSelfAdjoint u‖ ≤ ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUnitary_sub_one (key.trans <| norm_argSelfAdjoint_le_pi u)]
  trans 2 * (1 - Real.cos ‖argSelfAdjoint u‖)
  · gcongr
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (norm_argSelfAdjoint_le_pi u) key
  · exact (two_mul_one_sub_cos_norm_argSelfAdjoint hu).le

@[fun_prop]
lemma unitary.continuousOn_argSelfAdjoint :
    ContinuousOn (argSelfAdjoint : unitary A → selfAdjoint A) (ball (1 : unitary A) 2) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp [Function.comp_def]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le_of_lt (by positivity) huε
  have huε' : dist u 1 < √ε := Real.lt_sqrt_of_sq_lt huε
  apply ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_of_mem huε')
  apply ContinuousOn.image_comp_continuous ?_ continuous_subtype_val
  apply continuousOn_cfc A (s := sphere 0 1 ∩ {z | 2 * (1 - z.re) ≤ ε}) ?_ _ ?_ |>.mono
  · rintro - ⟨v, hv, rfl⟩
    simp only [Set.subset_inter_iff, Set.mem_setOf_eq]
    refine ⟨inferInstance, spectrum_subset_circle v, ?_⟩
    intro z hz
    simp only [Set.mem_setOf_eq]
    trans ‖(v - 1 : A)‖ ^ 2
    · exact two_mul_one_sub_le_norm_sub_one_sq v.2 hz
    · refine Real.le_sqrt (by positivity) (by positivity) |>.mp ?_
      simpa [Subtype.dist_eq, dist_eq_norm] using hv
  · exact isCompact_sphere 0 1 |>.inter_right <| isClosed_le (by fun_prop) (by fun_prop)
  · refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
    apply subset_slitPlane_of_subset_sphere Set.inter_subset_left
    norm_num at hε2 ⊢
    exact hε2

/-- the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`. -/
@[simps]
noncomputable def unitary.partialHomeomorph :
    PartialHomeomorph (unitary A) (selfAdjoint A) where
  toFun := argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos (1 - 2 ^ 2 / 2) := by
        apply Real.arccos_lt_arccos (by norm_num) (by gcongr)
        linarith [(by positivity : 0 ≤ ‖(u - 1 : A)‖ ^ 2 / 2)]
      _ = π := by norm_num
  map_target' x hx := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hx ⊢
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    rw [norm_sq_expUnitary_sub_one hx.le]
    have : -1 < Real.cos ‖(x : A)‖ :=
      Real.cos_pi ▸ Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
    simp [mul_sub, sq]
    linarith
  left_inv' u hu := expUnitary_argSelfAdjoint <| by
    simpa [Subtype.dist_eq, dist_eq_norm] using hu
  right_inv' x hx := argSelfAdjoint_expUnitary <| by simpa using hx
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

lemma unitary.norm_sub_eq (u v : unitary A) :
    ‖(u - v : A)‖ = ‖((u * star v : unitary A) - 1 : A)‖ := calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp

lemma unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) :
    expUnitary (argSelfAdjoint (u * star v)) = u * star v :=
  expUnitary_argSelfAdjoint <| norm_sub_eq u v ▸ huv

/-- For a selfadjoint element `x` in a C⋆-algebra, this is the path from `1` to `expUnitary x`. -/
@[simps]
noncomputable def selfAdjoint.expUnitary_pathToOne (x : selfAdjoint A) :
    Path 1 (expUnitary x) where
  toFun t := expUnitary ((t : ℝ) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
lemma selfAdjoint.joined_one_expUnitary (x : selfAdjoint A) :
    Joined (1 : unitary A) (expUnitary x) :=
  ⟨expUnitary_pathToOne x⟩

/-- The path `t ↦ expUnitary (t • argSelfAdjoint (v * star u)) * u`
from `u : unitary A` to `v` when `‖v - u‖ < 2`. -/
@[simps]
noncomputable def unitary.path (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Path u v where
  toFun t := expUnitary ((t : ℝ) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

lemma unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Joined u v :=
  ⟨path u v huv⟩

/-- Any ball of radius `δ < 2` in the unitary group of a unital C⋆-algebra is path connected. -/
lemma unitary.isPathConnected_ball (u : unitary A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (u : unitary A) δ) := by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
    convert this |>.image (f := (u * ·)) (by fun_prop)
    ext v
    rw [← inv_mul_cancel u]
    simp [- inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu ↦ ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [Subtype.dist_eq, dist_eq_norm] using hu
  refine ⟨path 1 u (hu.trans hδ₂), fun t ↦ ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm] using
    norm_expUnitary_smul_argSelfAdjoint_sub_one_le u t.2 (hu.trans hδ₂) |>.trans_lt hu

instance unitary.instLocPathConnectedSpace : LocPathConnectedSpace (unitary A) :=
  .of_bases (fun _ ↦ nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) <| by
    simpa using isPathConnected_ball

/-- The path component of the identity in the unitary group of a C⋆-algebra is the set of
unitaries that can be expressed as a product of exponentials of selfadjoint elements. -/
lemma unitary.mem_pathComponentOne_iff {u : unitary A} :
    u ∈ pathComponent 1 ↔ ∃ l : List (selfAdjoint A), (l.map expUnitary).prod = u := by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, (hlv : (l.map expUnitary).prod = v)⟩, huv⟩⟩ := hu
    refine ⟨argSelfAdjoint (u * star v) :: l, ?_⟩
    simp [hlv, mul_assoc, expUnitary_eq_mul_inv u v (by simpa [Subtype.dist_eq, dist_eq_norm] using huv)]
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => simp
    | cons x xs ih => simpa using (joined_one_expUnitary x).mul ih

end ExpUnitary
