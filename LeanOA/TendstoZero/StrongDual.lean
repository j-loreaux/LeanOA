import Mathlib.Analysis.Normed.Operator.Mul
import LeanOA.Lp.Holder
import LeanOA.TendstoZero.Defs

open scoped ENNReal tendstoZero lp

variable {ι 𝕜 : Type*} [RCLike 𝕜]

variable (ι 𝕜) in
/-- The map from `ℓ^p(ι, 𝕜)` to `StrongDual 𝕜 ℓ^q(ι, 𝕜)` when `p` and `q` are Hölder conjugate.
This should be upgraded to an isometry if `p ≠ ∞`, and, in case `1 < p ∨ 1 < q`, a linear isometry
equivalence. The map is given by `fun f g ↦ ∑' i, (f i) (g i)`. -/
noncomputable def lp.scalarDualPairing (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    ℓ^p(ι, 𝕜) →L[𝕜] StrongDual 𝕜 (ℓ^q(ι, 𝕜)) :=
  lp.dualPairing p q _ (K := 1) fun _ ↦ ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜

lemma lp.norm_scalarDualPairing {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    ‖lp.scalarDualPairing ι 𝕜 p q‖ ≤ 1 :=
  lp.norm_dualPairing ..

namespace tendstoZero

set_option backward.isDefEq.respectTransparency false in
variable (ι 𝕜) in
/-- The natural continuous linear map from `ℓ¹(ι, 𝕜)` into the (strong) dual of `c₀(ι, 𝕜)`
given by `fun x y ↦ ∑' i, (y i) * (x i)`. the order of the parameter is reversed because we
implement this via the `lp.scalarDualPairing` of `ℓ¹` with `ℓ^∞`, where we compose with the
inclusion of `c₀(ι, 𝕜)` into `ℓ^∞(ι, 𝕜)`. -/
noncomputable def lpOneToStrongDual :
    ℓ¹(ι, 𝕜) →L[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  .flip <| lp.scalarDualPairing ι 𝕜 ∞ 1 ∘L (subtypeₗᵢ 𝕜 _).toContinuousLinearMap

lemma lpOneToStrongDual_apply_apply
    (x : ℓ¹(ι, 𝕜)) (y : c₀(ι, 𝕜)) :
    lpOneToStrongDual ι 𝕜 x y = ∑' i, y.1 i * x i :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma norm_lpOneToStrongDual_apply (x : ℓ¹(ι, 𝕜)) :
    ‖lpOneToStrongDual ι 𝕜 x‖ ≤ ‖x‖ := by
  refine (lpOneToStrongDual ι 𝕜 x).opNorm_le_bound (by positivity) fun φ ↦ ?_
  rw [mul_comm, ← one_mul ‖φ‖]
  apply lp.scalarDualPairing ι 𝕜 ∞ 1 |>.le_opNorm₂ .. |>.trans
  gcongr
  · exact lp.norm_scalarDualPairing
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
lemma norm_lpOneToStrongDual : ‖lpOneToStrongDual ι 𝕜‖ ≤ 1 :=
  lpOneToStrongDual ι 𝕜 |>.opNorm_le_bound (by positivity) fun x ↦ by
    simpa only [one_mul] using norm_lpOneToStrongDual_apply x

set_option backward.isDefEq.respectTransparency false in
open ComplexOrder in
lemma sum_strongDual_eval_single_le_norm [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) (s : Finset ι) :
    ∑ i ∈ s, ‖φ (single i 1)‖ ≤ ‖φ‖ := by
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜), RCLike.ofReal_sum]
  have (c : 𝕜) : (‖c‖ : 𝕜) = (‖c‖ * c⁻¹) • c := by
    obtain (rfl | hc) := eq_or_ne c 0
    · simp
    · simp [hc]
  have h₁ : (∑ x ∈ s, ‖φ (single x 1)‖ : 𝕜) =
      φ (∑ x ∈ s, (‖φ (single x 1)‖ * (φ (single x 1))⁻¹) • single x 1) := by
    simp [-smul_eq_mul, ← this]
  have := RCLike.norm_of_nonneg' (K := 𝕜) (h₁ ▸ s.sum_nonneg (by simp))
  rw [h₁, ← this, RCLike.ofReal_le_ofReal, ← mul_one ‖φ‖]
  refine φ.le_opNorm_of_le ?_
  simp only [AddSubgroupClass.coe_norm, AddSubgroup.val_finset_sum, coe_smul, coe_single]
  refine lp.norm_le_of_forall_le (by positivity) fun i ↦ ?_
  simp only [AddSubgroup.val_finset_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    lp.single_apply, smul_eq_mul]
  by_cases! hi : i ∈ s
  · rw [s.sum_eq_single_of_mem i hi (by simp +contextual)]
    obtain (h | h) := eq_or_ne (φ (single i 1)) 0
    all_goals simp [h]
  · rw [s.sum_eq_zero]
    · simp
    · intro j hj
      have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
      simp [hij]

open ENNReal in
lemma strongDual_eval_single_memℓp_one [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) :
    Memℓp (fun i ↦ φ (single i 1)) 1 :=
  memℓp_gen' <| by simpa only [toReal_one, Real.rpow_one]
    using sum_strongDual_eval_single_le_norm φ

/-- The map from the (strong) dual of `c₀(ι, 𝕜)` to `ℓ¹(ι, 𝕜)` given by
`fun φ i ↦ φ (single i 1)`. This is the inverse of `tendstoZero.lpOneToStrongDual` -/
@[simps]
noncomputable def strongDualTolpOne [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) : ℓ¹(ι, 𝕜) :=
  ⟨fun i ↦ φ (single i 1), strongDual_eval_single_memℓp_one φ⟩

set_option backward.isDefEq.respectTransparency false in
lemma norm_strongDualTolpOne_apply [DecidableEq ι]
    (φ : StrongDual 𝕜 c₀(ι, 𝕜)) : ‖strongDualTolpOne φ‖ ≤ ‖φ‖ :=
  lp.norm_le_of_forall_sum_le (by simp) (by positivity) <| by
    simpa using sum_strongDual_eval_single_le_norm φ

-- one way to be more clever about this would be to use the fact that we actually have
-- *continuous* linear maps in both directions (it's easy to get the reverse direction to be
-- linear, and continuity follows from the bound above). Call these two maps `f` and `g`.
-- Then you say: since `span {lp.single}` is dense in `ℓ¹`, to show `g ∘ f = id`, it suffices
-- to check this on `lp.single`, which is trivial. Similarly, to show `f ∘ g = id`, take
-- any `φ` in the strong dual of `c₀`. To show that `f (g φ) = φ`, since `span {single}`
-- is dense in `c₀`, it suffices to show that `f (g φ) single = φ single`, which is similarly
-- straightforward. However, I don't think we have this helper theorem yet, and in any case,
-- the proof below is not too bad.
variable (ι 𝕜) in
/-- The (inverse) maps `tendstoZero.lpOneToStrongDual` and `tendstoZero.strongDualTolpOne`
bundled into a linear equivalence. This is only a stepping stone to construct the linear
isometry equivalence between these spaces. -/
@[simps!]
noncomputable def lpOneToStrongDualLinearEquiv [DecidableEq ι] :
    ℓ¹(ι, 𝕜) ≃ₗ[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  { (lpOneToStrongDual ι 𝕜).toLinearMap with
    invFun := strongDualTolpOne
    left_inv x := by
      ext i
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe,
        strongDualTolpOne_coe, lpOneToStrongDual_apply_apply]
      rw [tsum_eq_single i (fun j hj ↦ by simp [hj])]
      simp
    right_inv φ := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      ext x
      simp only [lpOneToStrongDual_apply_apply, strongDualTolpOne_coe]
      simp_rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
      exact φ.hasSum (hasSum_single x) |>.tsum_eq }

set_option backward.isDefEq.respectTransparency false in
variable (ι 𝕜) in
/-- The linear isometry equivalence between `ℓ¹(ι, 𝕜)` and the (strong) dual of `c₀(ι, 𝕜)`.
In the forward direction, this is given by `fun x y ↦ ∑' i, (y i) * (x i)`, and in the
backward direction this is given by `fun φ i ↦ φ (single i 1)`. -/
@[simps!]
noncomputable def lpOneToStrongDualₗᵢ [DecidableEq ι] :
    ℓ¹(ι, 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 c₀(ι, 𝕜) :=
  .ofBounds (lpOneToStrongDualLinearEquiv ι 𝕜) norm_lpOneToStrongDual_apply
    norm_strongDualTolpOne_apply

end tendstoZero
