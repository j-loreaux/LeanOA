import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import LeanOA.Lp.lpSpace
import LeanOA.ForMathlib.Misc


open scoped ENNReal NNReal Topology

variable {ι 𝕜 : Type*} {E : ι → Type*}
variable [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

open Filter

variable (E) in
-- maybe we want this to be a subgroup of `preLp`?
/-- The additive subgroup of `lp E ∞` consisting of those sequences whose norms converge
to zero. This has the notation `c₀ E` in the scope `tendstoZero`. In the special case
where `E := fun _ : ι → 𝕜`, the notation `c₀(ι, 𝕜)` is available. -/
def tendstoZero : AddSubgroup (lp E ∞) where
  carrier := {x | Tendsto (‖x ·‖) cofinite (𝓝 0)}
  add_mem' {x y} hx hy := tendsto_const_nhds.squeeze
    (by simpa using hx.add hy) (by simp [Pi.le_def]) (fun _ ↦ norm_add_le ..)
  zero_mem' := by simpa using tendsto_const_nhds
  neg_mem' := by simp

@[inherit_doc]
scoped [tendstoZero] notation "c₀" => tendstoZero
@[inherit_doc]
scoped [tendstoZero] notation "c₀(" ι ", " 𝕜 ")" => tendstoZero (fun _ : ι ↦ 𝕜)

open scoped tendstoZero

lemma mem_tendstoZero_iff (x : lp E ∞) :
    x ∈ c₀ E ↔ Tendsto (‖x ·‖) cofinite (𝓝 0) :=
  Iff.rfl

lemma lp.lipschitzWith_one_eval (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) :
    LipschitzWith 1 (fun x : lp E p ↦ x i) :=
  .mk_one fun x y ↦ by
    simp_rw [dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' ..

namespace tendstoZero

instance isClosed : IsClosed (c₀ E : Set (lp E ∞)) := by
  simp only [tendstoZero, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk,
    AddSubsemigroup.coe_set_mk]
  classical
  have (x : lp E ∞) : Tendsto (fun i ↦ ‖x i‖) cofinite (𝓝 0) ↔
      Tendsto (fun i ↦ (lp.single (E := E) ∞ i) (x i)) cofinite (𝓝 0) := by
    conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
    simp
  simp_rw [this]
  refine LipschitzWith.uniformEquicontinuous _ 1 (fun i ↦ ?_)
    |>.equicontinuous.isClosed_setOf_tendsto continuous_const
  simpa using lp.isometry_single i |>.lipschitz.comp <| lp.lipschitzWith_one_eval ∞ i

instance : SMul 𝕜 (c₀ E) where
  smul k x := ⟨k • x, by simpa [mem_tendstoZero_iff, norm_smul] using x.2.const_mul _⟩

@[simp]
lemma coe_smul (k : 𝕜) (x : c₀ E) : ↑(k • x) = k • (x : lp E ∞) := rfl

instance : Module 𝕜 (c₀ E) := fast_instance%
  Subtype.val_injective.module 𝕜 (c₀ E).subtype fun _ _ ↦ rfl

instance : NormedSpace 𝕜 (c₀ E) where
  norm_smul_le _ _ := norm_smul_le _ (_ : lp E ∞)

variable (𝕜 E) in
/-- The embedding of `c₀ E` into `lp E ∞` as a linear isometry. -/
def subtypeₗᵢ : c₀ E →ₗᵢ[𝕜] lp E ∞ where
  toFun := (↑)
  map_add' := by simp
  map_smul' := by simp
  norm_map' _ := rfl

variable (𝕜 E) in
/-- `c₀ E` as a `𝕜`-submodule of `lp E ∞`. -/
def toSubmodule : Submodule 𝕜 (lp E ∞) :=
  { c₀ E with
    smul_mem' c x hx := c • (⟨x, hx⟩ : c₀ E) |>.2 }

@[simp]
lemma toAddSubgroup_toSubmodule : (toSubmodule 𝕜 E).toAddSubgroup = c₀ E := rfl

end tendstoZero

namespace lp

variable {p : ℝ≥0∞}

variable (E) in
lemma range_addMonoidHomOfLE_top_le_tendstoZero (hp : p < ∞) :
    (addMonoidHomOfLE E hp.le).range ≤ c₀ E := by
  rintro - ⟨x, rfl⟩
  simp only [mem_tendstoZero_iff, coe_addMonoidHomOfLE_apply]
  obtain (rfl | hp') := eq_zero_or_pos p
  · exact tendsto_nhds_of_eventually_eq <| by simpa using memℓp_zero_iff.mp <| lp.memℓp x
  have hp'' := ENNReal.toReal_pos_iff.mpr ⟨hp', hp⟩
  have := lp.memℓp x |>.summable hp'' |>.tendsto_cofinite_zero
    |>.rpow_const (p := p.toReal⁻¹) (by aesop)
  rw [Real.zero_rpow (inv_pos.mpr hp'').ne'] at this
  convert this with i
  rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hp''.ne', Real.rpow_one]

variable (𝕜 E) in
lemma range_linearMapOfLE_top_le_tendstoZero (hp : p < ∞) :
    LinearMap.range (linearMapOfLE 𝕜 E (le_top (a := p))) ≤ tendstoZero.toSubmodule 𝕜 E := by
  simpa [← Submodule.toAddSubgroup_le, LinearMap.range_toAddSubgroup]
    using range_addMonoidHomOfLE_top_le_tendstoZero E hp

lemma topologicalClosure_range_addMonoidHomOfLE_top (hp : p < ∞) :
    (addMonoidHomOfLE E hp.le).range.topologicalClosure = c₀ E := by
  apply le_antisymm
    (AddSubgroup.topologicalClosure_minimal _ (range_addMonoidHomOfLE_top_le_tendstoZero E hp)
      tendstoZero.isClosed)
  suffices c₀ E ≤ (addMonoidHomOfLE E (zero_le ∞)).range.topologicalClosure by
    apply this.trans <| AddSubgroup.topologicalClosure_mono ?_
    rw [← addMonoidHomOfLE_comp (zero_le p) hp.le, AddMonoidHom.range_comp]
    exact AddSubgroup.map_le_range ..
  intro x hx
  rw [mem_tendstoZero_iff] at hx
  rw [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range,
    mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall]
  simp only [Set.exists_range_iff, Metric.mem_closedBall]
  intro ε hε
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff] at hx
  specialize hx ε hε
  rw [Filter.eventually_cofinite] at hx
  classical
  let y : lp E 0 :=
    ⟨fun i ↦ if ε < ‖x i‖ then x i else 0, memℓp_zero_iff.mpr <| hx.subset <| by aesop⟩
  refine ⟨y, ?_⟩
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le hε.le fun i ↦ ?_
  by_cases! hi : ‖x i‖ ≤ ε
  · simpa [y, hi.not_gt]
  · simpa [y, hi] using hε.le

end lp

namespace tendstoZero

variable [DecidableEq ι]

lemma single_mem (i : ι) (c : E i) :
    lp.single ∞ i c ∈ c₀ E :=
  lp.range_addMonoidHomOfLE_top_le_tendstoZero E ENNReal.zero_lt_top ⟨lp.single 0 i c, by ext; simp⟩

/-- `lp.single` as an element of `c₀ E`. -/
def single (i : ι) (c : E i) : c₀ E :=
  ⟨lp.single ∞ i c, single_mem i c⟩

@[simp]
lemma coe_single (i : ι) (c : E i) :
    (tendstoZero.single i c : lp E ∞) = lp.single ∞ i c :=
  rfl

lemma smul_single (i : ι) (c : 𝕜) (x : E i) :
    c • single i x = single i (c • x) := by
  ext; simp [single]

open Filter Topology in
lemma hasSum_single (x : c₀ E) :
    HasSum (fun i ↦ single i (x.1 i)) x := by
  have hx := mem_tendstoZero_iff _ |>.mp x.2
  rw [HasSum]
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff] at hx ⊢
  peel hx with ε hε hx
  rw [Filter.eventually_cofinite] at hx
  simp only [Metric.mem_closedBall, dist_zero_right, norm_norm, not_le] at hx
  filter_upwards [Filter.atTop_basis.mem_of_mem (i := hx.toFinset) trivial] with s hs
  simp only [Metric.mem_closedBall, dist_eq_norm]
  refine lp.norm_le_of_forall_le hε.le fun i ↦ ?_
  simp only [AddSubgroup.subtype_apply, AddSubgroupClass.coe_sub, AddSubgroup.val_finset_sum,
    coe_single, Pi.sub_apply, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]
  split_ifs with hi
  · simpa using hε.le
  · simpa using Set.notMem_subset hs hi

end tendstoZero
