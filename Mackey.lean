import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded


namespace LinearMap

open scoped Pointwise

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

lemma polar_smul (s : Set E) (c : 𝕜) (hc : c ≠ 0) : B.polar (c • s) = c⁻¹ • B.polar s := by
  ext x
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  simp [polar, Set.mem_smul_set]
  simp [← Units.smul_def, smul_eq_iff_eq_inv_smul, ← Units.val_inv_eq_inv_val]
  simp [Units.smul_def]
  -- clean up later.

end LinearMap

section Banach_Alaoglu

variable (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜]

open Set Topology WeakDual Metric

-- is this the right generality?
theorem Bornology.isVonNBounded_image (s : Set E) {f : E → 𝕜} {r : ℝ}
    (hf : ∀ u ∈ s, ‖f u‖ ≤ r) : Bornology.IsVonNBounded 𝕜 (f '' s) := by
  aesop (add simp NormedSpace.isVonNBounded_iff')

variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

-- what's the right generality for this?
variable (E) in
theorem WeakDual.isInducing_dFunLikeCoe :
    IsInducing (DFunLike.coe : WeakDual 𝕜 E → (E → 𝕜)) where eq_induced := rfl

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

-- deprime and replace the original
lemma WeakDual.isClosed_image_polar_of_mem_nhds' {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsClosed (DFunLike.coe '' polar 𝕜 s) :=
  have : DFunLike.coe '' polar 𝕜 s = {f : E → 𝕜 | ∀ (x y : E), f (x + y) = f x + f y} ∩
      {f : E → 𝕜 | ∀ (c : 𝕜) (x : E), f (c • x) = c • f x} ∩
        ⋂ u ∈ s, (fun f : E → 𝕜 => ‖f u‖) ⁻¹' Set.Iic 1 := by
    refine subset_antisymm_iff.mpr ⟨fun _ hf ↦ ?_, fun f ↦ ?_⟩
    · rcases hf with ⟨φ, hφ, rfl⟩; simpa
    simpa using fun hf1 hf2 hf3 ↦ ⟨LinearMap.clmOfExistsBoundedImage
        { toFun := f, map_add' := hf1, map_smul' := hf2 }
        ⟨s, s_nhds, Bornology.isVonNBounded_image 𝕜 s hf3⟩,
      mem_preimage.mp hf3, rfl⟩
  this ▸ ((isClosed_setOf_map_add E 𝕜).inter (isClosed_setOf_map_smul E 𝕜 id)).inter
    (isClosed_biInter fun u _ ↦ isClosed_Iic.preimage (continuous_apply u).norm)

-- deprime and replace the original
theorem WeakDual.isCompact_polar' [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsCompact (polar 𝕜 s) := by
  suffices IsCompact (DFunLike.coe '' polar 𝕜 s) by
    simpa [(DFunLike.coe_injective (β := fun _ ↦ 𝕜)).preimage_image <| polar 𝕜 s] using
      (WeakDual.isInducing_dFunLikeCoe 𝕜 E).isCompact_preimage' this
  obtain ⟨r, hr⟩ : ∃ r : E → ℝ,
      DFunLike.coe '' polar 𝕜 s ⊆ univ.pi fun v ↦ Metric.closedBall 0 (r v) := by
    suffices ∀ v : E, ∃ r : ℝ, ∀ φ ∈ polar 𝕜 s, ‖φ v‖ ≤ r by
      choose r hr using this
      aesop (add simp subset_def)
    intro v
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff (s := (fun x : 𝕜 ↦ x • v) ⁻¹' s) (x := 0).mp <| by
      simpa using Continuous.continuousAt (by fun_prop) (by simpa)
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt 𝕜 hε
    refine ⟨1 / ‖c‖, fun φ hφ ↦ ?_⟩
    simpa only [le_div_iff₀ hc0, mul_comm, ← norm_smul, map_smul] using hφ _ (h (by simpa using hc))
  exact (isCompact_univ_pi <| fun i ↦ ProperSpace.isCompact_closedBall 0 (r i)).of_isClosed_subset
    (isClosed_image_polar_of_mem_nhds' 𝕜 s_nhds) hr

end Banach_Alaoglu

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity
open scoped UniformConvergenceCLM

namespace LinearMap

public section

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommMonoid F] [Module 𝕜 F]

class IsCompatible (B : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) : Prop where
  range_eq_range : B.range = (ContinuousLinearMap.coeLM 𝕜).range
  injective : Function.Injective B

-- TODO: show that any `F ≃ₗ[𝕜] StrongDual 𝕜 E` yields an `IsCompatible` instance.

lemma IsCompatible.continuous (B : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) [h : B.IsCompatible]
    (x : F) : Continuous (B x) :=
  have ⟨y, hy⟩ := Submodule.ext_iff.mp h.range_eq_range (B x) |>.mp (B.mem_range_self x)
  hy ▸ y.continuous

noncomputable def IsCompatible.equiv (B : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) [h : B.IsCompatible] :
    F ≃ₗ[𝕜] StrongDual 𝕜 E :=
  .ofBijective
    { toFun x := ⟨B x, h.continuous B x⟩,
      map_add' _ _ := by ext; simp,
      map_smul' _ _ := by ext; simp }
    ⟨fun _ _ ↦ by simp [h.injective.eq_iff], fun x ↦
      have ⟨y, hy⟩ := h.range_eq_range ▸ LinearMap.mem_range_self _ x
      ⟨y, ContinuousLinearMap.ext fun _ ↦ congr($hy _)⟩⟩

end

section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommMonoid F] [Module 𝕜 F]

lemma IsCompatible.equiv_apply (B : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) [h : IsCompatible B]
    (x : F) : h.equiv B x = ⟨B x, h.continuous B x⟩ := rfl

@[simp] lemma IsCompatible.equiv_apply_apply (B : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) [h : IsCompatible B]
    (x : F) (y : E) : h.equiv B x y = B x y := rfl

end

end LinearMap

section -- unneeded on current master

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
  {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F]
variable (F)

@[inherit_doc]
scoped[UniformConvergenceCLM]
notation:25 E' " →SLᵤ[" σ ", " 𝔖 "] " F => UniformConvergenceCLM σ (E := E') F 𝔖

@[inherit_doc]
scoped[UniformConvergenceCLM]
notation:25 E' " →Lᵤ[" R ", " 𝔖 "] " F => UniformConvergenceCLM (RingHom.id R) (E := E') F 𝔖

end

namespace UniformOnFun

variable {α β R : Type*} (𝔖 : Set (Set α))

/-- `UniformOnFun.toFun` as a linear equivalence. -/
@[simps!]
def toFunAddEquiv [AddCommMonoid β] : (α →ᵤ[𝔖] β) ≃+ (α → β) where
  toEquiv := toFun 𝔖
  map_add' _ _ := rfl

/-- `UniformOnFun.toFun` as an additive group equivalence. -/
@[simps!]
def toFunLinearEquiv [Semiring R] [AddCommMonoid β] [Module R β] :
    (α →ᵤ[𝔖] β) ≃ₗ[R] (α → β) where
  toAddEquiv := toFunAddEquiv 𝔖
  map_smul' _ _ := rfl


---------- This is nonsense and unprovable, *BUT* where it is used later is fixable. ------------

variable {𝔖}
variable {𝕜 : Type*} [NormedField 𝕜] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

variable (𝕜) in
/-- The seminorm given by taking the supremum of the norms over a set in the collection.

Note: if `f` is unbounded on `s`, this seminorm takes the value zero. -/
noncomputable def seminorm (s : Set α) (hs : s ∈ 𝔖) :
    Seminorm 𝕜 (α →ᵤ[𝔖] β) where
  toFun f := ⨆ x : s, ‖toFun 𝔖 f x‖
  map_zero' := by simp
  add_le' := sorry
  neg' := by simp
  smul' := by simp [norm_smul, Real.mul_iSup_of_nonneg (norm_nonneg _)]

lemma seminorm_apply (s : Set α) (hs : s ∈ 𝔖) (f : α →ᵤ[𝔖] β) :
    seminorm 𝕜 s hs f = ⨆ x : s, ‖toFun 𝔖 f x‖ := rfl

variable (𝕜 α β 𝔖) in
/-- lazy -/
noncomputable def seminormFamily : SeminormFamily 𝕜 (α →ᵤ[𝔖] β) 𝔖 :=
  fun s ↦ seminorm 𝕜 s.1 s.2

lemma seminormFamily_apply (s : 𝔖) (f : α →ᵤ[𝔖] β) :
    seminormFamily α β 𝔖 𝕜 s f = ⨆ x : s.1, ‖toFun 𝔖 f x‖ := rfl

---------- End broken part ------------

end UniformOnFun

section PolarTopology

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

set_option linter.unusedVariables false in
/-- `PolarTopology B 𝔖`, where `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is a type synonym for `E` where the topology
is induced by `B` when we equip `F → 𝕜` with the topology of uniform convergence on the collection
of sets `𝔖 : Set (Set F))`. -/
@[nolint unusedArguments]
def PolarTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) := E
deriving AddCommGroup, Module 𝕜

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) :
    Module 𝕝 (PolarTopology B 𝔖) :=
  ‹Module 𝕝 E›

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] [SMul 𝕝 𝕜] [IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) :
    IsScalarTower 𝕝 𝕜 (PolarTopology B 𝔖) :=
  ‹IsScalarTower 𝕝 𝕜 E›

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F))

namespace PolarTopology

open UniformOnFun Topology

variable {B 𝔖} in
/-- The canonical equivalence between `PolarTopology B 𝔖` and `E`. -/
def linearEquiv : PolarTopology B 𝔖 ≃ₗ[𝕜] E := .refl _ _

-- TODO: maybe this should be a `ContinuousLinearMap`.
variable {B 𝔖} in
/-- The map from `PolarTopology B 𝔖` to `F →ᵤ[𝔖] 𝕜` which induces the uniformity. -/
@[simps!]
def toUniformOnFun : PolarTopology B 𝔖 →ₗ[𝕜] F →ᵤ[𝔖] 𝕜 :=
  linearEquiv.symm.arrowCongr (UniformOnFun.toFunLinearEquiv 𝔖).symm <|
    (LinearMap.ltoFun 𝕜 F 𝕜 𝕜).compRight 𝕜 B

instance : UniformSpace (PolarTopology B 𝔖) :=
  .comap (fun x : PolarTopology B 𝔖 ↦ UniformOnFun.ofFun 𝔖 ⇑(B x)) inferInstance

lemma isUniformInducing_toUniformOnFun : IsUniformInducing (toUniformOnFun (B := B) (𝔖 := 𝔖)) where
  comap_uniformity := rfl

lemma isUniformEmbedding_toUniformOnFun (hB : B.SeparatingLeft) :
    IsUniformEmbedding (toUniformOnFun (B := B) (𝔖 := 𝔖)) where
  comap_uniformity := rfl
  injective := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hx
      apply ofFun 𝔖 |>.injective at hx
      simp only [LinearEquiv.coe_coe, LinearMap.compRight_apply, LinearMap.coe_comp,
        LinearEquiv.symm_symm, comp_apply, LinearMap.ltoFun_apply,
        toFunLinearEquiv_symm_apply, funext_iff] at hx
      apply hB
      exact (hx ·)
    · rintro rfl; exact map_zero _

open scoped Uniformity Topology
open UniformOnFun

variable {𝔖}

lemma hasBasis_uniformity_of_basis {ι : Type*} {p : ι → Prop} {s : ι → Set (𝕜 × 𝕜)}
    (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) (hb : (𝓤 𝕜).HasBasis p s) :
    (𝓤 (PolarTopology B 𝔖)).HasBasis
      (fun (Si : Set F × ι) ↦ Si.1 ∈ 𝔖 ∧ p Si.2)
      (fun (Si : Set F × ι) ↦
        (Prod.map toUniformOnFun toUniformOnFun) ⁻¹' (UniformOnFun.gen 𝔖 Si.1 (s Si.2))) :=
  UniformOnFun.hasBasis_uniformity_of_basis F 𝕜 𝔖 h h' hb |>.comap _

lemma hasBasis_uniformity (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓤 (PolarTopology B 𝔖)).HasBasis
      (fun (SV : Set F × Set (𝕜 × 𝕜)) ↦ SV.1 ∈ 𝔖 ∧ SV.2 ∈ uniformity 𝕜)
      (fun (SV : Set F × Set (𝕜 × 𝕜)) ↦
        (Prod.map toUniformOnFun toUniformOnFun) ⁻¹' (UniformOnFun.gen 𝔖 SV.1 SV.2)) :=
  UniformOnFun.hasBasis_uniformity F 𝕜 𝔖 h h' |>.comap _

variable {B}

lemma hasBasis_nhds_of_basis {ι : Type*} {p : ι → Prop} {s : ι → Set (𝕜 × 𝕜)}
    (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) (hb : (𝓤 𝕜).HasBasis p s)
    (y : PolarTopology B 𝔖) :
    (𝓝 y).HasBasis
      (fun (Si : Set F × ι) ↦ Si.1 ∈ 𝔖 ∧ p Si.2)
      (fun (Si : Set F × ι) ↦
        toUniformOnFun ⁻¹' {x | (x, toUniformOnFun y) ∈ UniformOnFun.gen 𝔖 Si.1 (s Si.2)}) := by
  rw [(isUniformInducing_toUniformOnFun B 𝔖).isInducing.nhds_eq_comap]
  exact UniformOnFun.hasBasis_nhds_of_basis F 𝕜 𝔖 _ h h' hb |>.comap _

lemma tendsto_iff {α : Type*} {f : α → PolarTopology B 𝔖} {l : Filter α} {y : PolarTopology B 𝔖} :
    Tendsto f l (𝓝 y) ↔
      ∀ s ∈ 𝔖, TendstoUniformlyOn (fun x ↦ B (linearEquiv (f x))) (B (linearEquiv y)) l s := by
  rw [(isUniformInducing_toUniformOnFun B 𝔖).isInducing.tendsto_nhds_iff,
    UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

variable (B) in
/-- The seminorm on `PolarTopology B 𝔖` by taking for `x : E` the supremum of the values of
`B x y` over all `y ∈ s`, where `s ∈ 𝔖`. -/
noncomputable def seminorm (s : Set F) (hs : s ∈ 𝔖) : Seminorm 𝕜 (PolarTopology B 𝔖) :=
  (UniformOnFun.seminorm 𝕜 s hs).comp toUniformOnFun
  --- TODO: this construction of the seminorm doesn't work because it is not a seminorm on
  --- `UniformOnFun`. We'll need that `s ∈ 𝔖` is compact in `WeakBilin B.flip`.

lemma seminorm_apply (s : Set F) (hs : s ∈ 𝔖) (x : PolarTopology B 𝔖) :
    seminorm B s hs x = ⨆ y : s, ‖B (linearEquiv x) y‖ := by
  rfl

variable (B 𝔖) in
noncomputable def seminormFamily : SeminormFamily 𝕜 (PolarTopology B 𝔖) 𝔖 :=
  (UniformOnFun.seminormFamily F 𝕜 𝔖 𝕜).comp toUniformOnFun

lemma seminormFamily_apply (s : 𝔖) :
    seminormFamily B 𝔖 s = seminorm B s.1 s.2 := by
  rfl

variable (B 𝔖) in
lemma withSeminorms : WithSeminorms (seminormFamily B 𝔖) :=  by
  rw [seminormFamily]
  apply (isUniformInducing_toUniformOnFun B 𝔖).isInducing.withSeminorms
  sorry

open scoped ComplexOrder

instance [Module ℝ E] [h : IsScalarTower ℝ 𝕜 E] : LocallyConvexSpace ℝ (PolarTopology B 𝔖) :=
  (withSeminorms B 𝔖).toLocallyConvexSpace

variable (B) in
/-- The collection of polars of neighborhoods of zero. -/
def nhdsPolars [TopologicalSpace E] : Set (Set F) := B.polar '' (𝓝 0).sets

lemma nhdsPolars_mem_iff [TopologicalSpace E] {s : Set F} :
  s ∈ nhdsPolars B ↔ s ∈ B.polar '' (𝓝 0).sets := Eq.to_iff rfl

instance : IsUniformAddGroup (PolarTopology B 𝔖) :=
  IsUniformInducing.isUniformAddGroup _ (isUniformInducing_toUniformOnFun _ _)

instance : ContinuousConstSMul 𝕜 (PolarTopology B 𝔖) :=
  isUniformInducing_toUniformOnFun B 𝔖 |>.isInducing.continuousConstSMul id <| by simp

lemma polar_mem_nhdsPolars [TopologicalSpace E] {s : Set E} (hs : s ∈ 𝓝 0) :
    B.polar s ∈ nhdsPolars B :=
  ⟨s, hs, rfl⟩

variable (B) in
lemma continuousAt_zero_seminorm [TopologicalSpace E] [ContinuousSMul 𝕜 E]
    {s : Set E} (hs1 : s ∈ 𝓝 0) :
    ContinuousAt (Seminorm.comp ((seminorm B (B.polar s) (polar_mem_nhdsPolars hs1)))
      (linearEquiv.symm).toLinearMap) 0 := by
  refine Seminorm.continuousAt_zero' (r := 1) <| mem_of_superset hs1 fun x hx ↦ ?_
  simp only [Seminorm.mem_closedBall, sub_zero, Seminorm.comp_apply, LinearEquiv.coe_coe,
    seminorm_apply, LinearEquiv.apply_symm_apply]
  apply csSup_le (range_nonempty (h := ⟨0, by simp⟩) _)
  rintro - ⟨⟨y, hy⟩, rfl⟩
  exact B.polar_mem s y hy x hx

/-- The continuous linear equivalence between `E` satisfiying `B.flip.IsCompatible` and
`PolarTopology B (nhdsPolars B)`. -/
def polarTopologyNhdsPolars [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E]
    [B.flip.IsCompatible] :
    PolarTopology B (nhdsPolars B) ≃L[𝕜] E where
  toLinearEquiv := linearEquiv (B := B) (𝔖 := nhdsPolars B)
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    sorry
  continuous_invFun := by
    simp only [LinearEquiv.invFun_eq_symm]
    apply (withSeminorms B (nhdsPolars B)).continuous_of_continuous_comp _
    rintro ⟨-, ⟨s, (hs : s ∈ 𝓝 0), rfl⟩⟩
    exact Seminorm.continuous_of_continuousAt_zero <| continuousAt_zero_seminorm B hs

end PolarTopology

end PolarTopology
