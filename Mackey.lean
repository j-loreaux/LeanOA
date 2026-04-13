import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms



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

variable {𝔖}
variable {𝕜 : Type*} [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β]

variable (𝕜) in
/-- The seminorm given by taking the supremum of the norms over a set in the collection.

Note: if `f` is unbounded on `s`, this seminorm takes the value zero. -/
noncomputable def seminorm (s : Set α) (hs : s ∈ 𝔖) :
    Seminorm 𝕜 (α →ᵤ[𝔖] β) where
  toFun f := ⨆ x ∈ s, ‖toFun 𝔖 f x‖
  map_zero' := by simp
  add_le' := sorry
  neg' := by simp
  smul' := sorry

lemma seminorm_apply (s : Set α) (hs : s ∈ 𝔖) (f : α →ᵤ[𝔖] β) :
    seminorm 𝕜 s hs f = ⨆ x ∈ s, ‖toFun 𝔖 f x‖ := rfl

variable (𝕜 α β 𝔖) in
/-- lazy -/
noncomputable def seminormFamily : SeminormFamily 𝕜 (α →ᵤ[𝔖] β) 𝔖 :=
  fun s ↦ seminorm 𝕜 s.1 s.2

lemma seminormFamily_apply (s : 𝔖) (f : α →ᵤ[𝔖] β) :
    seminormFamily α β 𝔖 𝕜 s f = ⨆ x ∈ s.1, ‖toFun 𝔖 f x‖ := rfl


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

lemma seminorm_apply (s : Set F) (hs : s ∈ 𝔖) (x : PolarTopology B 𝔖) :
    seminorm B s hs x = ⨆ y ∈ s, ‖B (linearEquiv x) y‖ := by
  rfl

variable (B 𝔖) in
noncomputable def seminormFamily : SeminormFamily 𝕜 (PolarTopology B 𝔖) 𝔖 :=
  (UniformOnFun.seminormFamily F 𝕜 𝔖 𝕜).comp toUniformOnFun

lemma seminormFamily_apply (s : 𝔖) (x : PolarTopology B 𝔖) :
    seminormFamily B 𝔖 s x = ⨆ y ∈ s.1, ‖B (linearEquiv x) y‖ := by
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

/-- The continuous linear equivalence between `E` satisfiying `B.flip.IsCompatible` and
`PolarTopology B (nhdsPolars B)`. -/
def polarTopologyNhdsPolars [TopologicalSpace E] [IsTopologicalAddGroup E]
    [B.flip.IsCompatible] :
    PolarTopology B (nhdsPolars B) ≃L[𝕜] E where
  toLinearEquiv := linearEquiv (B := B) (𝔖 := nhdsPolars B)
  continuous_toFun := by sorry
  continuous_invFun := by
    change Continuous linearEquiv.symm.toLinearMap
    apply (withSeminorms B (nhdsPolars B)).continuous_of_continuous_comp _ fun s ↦ ?_
    obtain ⟨-, ⟨s, (hs : s ∈ 𝓝 0), rfl⟩⟩ := s
    eta_expand
    simp only [Seminorm.comp_apply, LinearEquiv.coe_coe, seminormFamily_apply,
      LinearEquiv.apply_symm_apply]
    change Continuous fun x ↦ ⨆ y ∈ B.polar s, ‖(B x) y‖ -- avoid `Set` defeq abuse.

    sorry

end PolarTopology

end PolarTopology
