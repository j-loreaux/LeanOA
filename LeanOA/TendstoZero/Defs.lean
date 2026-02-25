import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import LeanOA.Lp.lpSpace
import LeanOA.Mathlib.Misc


open scoped ENNReal NNReal Topology

variable {ι 𝕜 : Type*} {E : ι → Type*}

section NormedRing

variable [NormedRing 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

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

namespace tendstoZero

/-- Constructor for a term of `c₀ E` which doesn't force the user to pass through `lp E ∞`. -/
def mk {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) :
    c₀ E :=
  ⟨⟨f, memℓp_infty h.bddAbove_range_of_cofinite⟩, h⟩

@[simp]
lemma coe_mk {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) :
    ⇑(mk f h : lp E ∞) = f :=
  rfl

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

noncomputable instance : SMul 𝕜 (c₀ E) where
  smul k x := ⟨k • x, squeeze_zero (fun _ ↦ by positivity)
    (fun i ↦ norm_smul_le k ((x : lp E ∞) i)) <| by simpa using Tendsto.const_mul ‖k‖ x.2⟩

@[simp]
lemma coe_smul (k : 𝕜) (x : c₀ E) : ↑(k • x) = k • (x : lp E ∞) := rfl

noncomputable instance : Module 𝕜 (c₀ E) := fast_instance%
  Subtype.val_injective.module 𝕜 (c₀ E).subtype fun _ _ ↦ rfl

instance : IsBoundedSMul 𝕜 (c₀ E) := .of_norm_smul_le (fun _ _ ↦ norm_smul_le _ (_ : lp E ∞))

noncomputable instance {ι 𝕜 : Type*} {E : ι → Type*} [NormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (c₀ E) where
  norm_smul_le := norm_smul_le

section MoreScalars

variable {𝕜' : Type*} [NormedRing 𝕜'] [∀ i, Module 𝕜' (E i)] [∀ i, IsBoundedSMul 𝕜' (E i)]

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (c₀ E) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_comm _ _ _⟩

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (c₀ E) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_assoc _ _ _⟩

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (c₀ E) :=
  ⟨fun _ _ => Subtype.ext <| op_smul_eq_smul _ _⟩

end MoreScalars

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

variable (𝕜 E) in
/-- The linear isometry equivalence between `c₀ E` and itself, viewed as a
submodule of `lp E ∞` (as opposed to only an `AddSubgroup`). -/
noncomputable def toSubmoduleLinearIsometryEquiv : toSubmodule 𝕜 E ≃ₗᵢ[𝕜] c₀ E :=
  LinearIsometryEquiv.refl ..

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

end NormedRing

section NontriviallyNormedField

open scoped tendstoZero

variable {F : ι → Type*}
variable [NontriviallyNormedField 𝕜]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- `c₀ E` is invariant under `lp.mapCLM`. -/
lemma lp.mapCLM_mem_tendstoZero (T : ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) (x : lp E ∞) (hx : x ∈ c₀ E) :
    lp.mapCLM ∞ T hK hTK x ∈ c₀ F :=
  tendsto_const_nhds.squeeze (mul_zero K ▸ hx.const_mul K) (fun _ ↦ by simp)
    fun i ↦ (T i).le_of_opNorm_le (hTK i) _

/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `c₀` space. -/
@[simps!]
noncomputable def tendstoZero.mapCLM (T : ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    c₀ E →L[𝕜] c₀ F :=
  letI e₁ := tendstoZero.subtypeₗᵢ 𝕜 E |>.toContinuousLinearMap
  letI e₂ := lp.mapCLM ∞ T hK hTK
  letI e₃ := toSubmoduleLinearIsometryEquiv 𝕜 F
    |>.symm.toContinuousLinearEquiv.toContinuousLinearMap
  e₃ ∘L ((e₂ ∘L e₁).codRestrict (tendstoZero.toSubmodule 𝕜 F)
    fun x ↦ lp.mapCLM_mem_tendstoZero T hK hTK x.1 x.2)

end NontriviallyNormedField
