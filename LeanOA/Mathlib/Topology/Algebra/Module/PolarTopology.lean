module

public import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar
public import LeanOA.Mathlib.Analysis.LocallyConvex.WeakBilin
public import LeanOA.Mathlib.Analysis.LocallyConvex.WithSeminorms
public import LeanOA.Mathlib.Topology.Algebra.UniformConvergence
public import LeanOA.LocallyConvexNhdsBasis
public import LeanOA.Mathlib.Topology.Algebra.Module.LinearMap
public import LeanOA.Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM
public import Mathlib.Data.Fintype.Order -- only needed for the finite union result


@[expose] public section

open ContinuousLinearMap Module
open scoped Topology

namespace LinearMap

open scoped Pointwise Topology
open WeakBilin Bornology

lemma absorbent_polar_iff_isVonNBounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}
    {s : Set (WeakBilin B)} :
    Absorbent 𝕜 ((pairing B).polar s) ↔ IsVonNBounded 𝕜 s := by
  rw [absorbent_iff_eventually_nhdsNE_zero]
  have : ∀ y, ∀ᶠ (c : 𝕜) in 𝓝[≠] 0,
      c • y ∈ (pairing B).polar s ↔ ∀ x ∈ s, ‖pairing B x y‖ ≤ ‖c⁻¹‖ := by
    intro y
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [norm_inv, smul_mem_polar_iff _ _ _ hc]
  conv in ∀ᶠ _ in _, _ =>
    rw [Filter.eventually_congr (this _), ← Filter.inv_cobounded₀, Filter.eventually_inv]
    simp only [inv_inv]
  rw [WeakBilin.isVonNBounded_iff]
  congr! 1 with y
  rw [NormedSpace.image_isVonNBounded_iff, ← comap_norm_atTop]
  rw [Filter.atTop_basis.comap _ |>.eventually_iff]
  simp only [Set.mem_preimage, Set.mem_Ici, true_and]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨r', hr'⟩ := NormedField.exists_lt_norm 𝕜 r
    exact ⟨‖r'‖, by simp; grind⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by simp at hr; grind⟩

alias ⟨isVonNBounded_of_absorbent_polar, absorbent_polar⟩ := absorbent_polar_iff_isVonNBounded

section nhdsPolars

open Set Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

variable (B) in
/-- The collection of polars of neighborhoods of zero. -/
def nhdsPolars [TopologicalSpace E] : Set (Set F) :=
  B.polar '' (𝓝 0).sets

lemma nonempty_nhdsPolars [TopologicalSpace E] : (nhdsPolars B).Nonempty :=
  Set.Nonempty.image _ ⟨univ, univ_mem⟩

lemma directedOn_nhdsPolars [TopologicalSpace E] : DirectedOn (· ⊆ ·) (nhdsPolars B) := by
  rintro - ⟨s₁, (hs₁ : s₁ ∈ 𝓝 0), rfl⟩ - ⟨s₂, (hs₂ : s₂ ∈ 𝓝 0), rfl⟩
  refine ⟨_, ⟨s₁ ∩ s₂, inter_mem hs₁ hs₂, rfl⟩, ?_, ?_⟩
  all_goals exact LinearMap.polar_antitone _ <| by simp

lemma nhdsPolars_mem_iff [TopologicalSpace E] {s : Set F} :
    s ∈ nhdsPolars B ↔ ∃ u ∈ 𝓝 0, B.polar u = s :=
  Eq.to_iff rfl

lemma polar_mem_nhdsPolars [TopologicalSpace E] {s : Set E} (hs : s ∈ 𝓝 0) :
    B.polar s ∈ nhdsPolars B :=
  ⟨s, hs, rfl⟩

end nhdsPolars

section Banach_Alaoglu

open WeakBilin Topology in
theorem IsCompatibleDual.isCompact_polar {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [ProperSpace 𝕜] [TopologicalSpace F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual] [hB : B.flip.IsWeak] {s : Set E}
    (s_nhds : s ∈ 𝓝 0) : IsCompact (B.polar s) := by
  simpa [ContinuousLinearEquiv.image_eq_preimage_symm] using
    WeakDual.isCompact_polar' _ s_nhds |>.image h.weakDualCLE'.symm.continuous

instance {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    [B.IsCompatibleDual] :
    LinearMap.IsCompatibleDual (pairing B.flip).flip :=
  WeakBilin.linearEquiv _ B.flip ≪≫ₗ LinearMap.IsCompatibleDual.equiv B |>.IsCompatibleDual _ rfl

--- there's a proof of this that doesn't use compactness (hence properness of `𝕜`) using the fact
--- that a set is von Neumann bounded if and only if its polar is absorbent.
open WeakBilin Topology in
theorem IsCompatibleDual.isVonNBounded_polar {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [ProperSpace 𝕜] [TopologicalSpace F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual] [hB : B.flip.IsWeak]
    {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsVonNBounded 𝕜 (B.polar s) := by
  rw [LinearMap.IsWeak.isVonNBounded_iff_bddAbove B.flip]
  exact fun x ↦ h.isCompact_polar _ s_nhds |>.bddAbove_image
    (LinearMap.IsWeak.continuous_eval B.flip x).norm.continuousOn

end Banach_Alaoglu

end LinearMap

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity
open scoped UniformConvergenceCLM

section PolarTopology

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

set_option linter.unusedVariables false in
/-- `PolarTopology B 𝔖`, where `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is a type synonym for `E` where the topology
is induced by `B` when we equip `F → 𝕜` with the topology of uniform convergence on the collection
of sets `𝔖 : Set (Set F))`. -/
@[nolint unusedArguments]
def PolarTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) := E
deriving AddCommGroup

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (𝔖 : Set (Set F)) :
    Module 𝕝 (PolarTopology B 𝔖) :=
  inferInstanceAs (Module 𝕝 E)

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] [SMul 𝕝 𝕜] [IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) :
    IsScalarTower 𝕝 𝕜 (PolarTopology B 𝔖) :=
  inferInstanceAs (IsScalarTower 𝕝 𝕜 E)

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F))

namespace PolarTopology

open UniformOnFun Topology WeakBilin

open scoped UniformConvergenceCLM

variable {B 𝔖} in
/-- The canonical equivalence between `PolarTopology B 𝔖` and `E`. -/
def linearEquiv : PolarTopology B 𝔖 ≃ₗ[𝕜] E := .refl _ _

/-- Variant of `B.flip` with the type synonym `PolarTopology B 𝔖` in place of `E`. -/
abbrev bilin : F →ₗ[𝕜] PolarTopology B 𝔖 →ₗ[𝕜] 𝕜 :=
  (linearEquiv.symm.arrowCongr (.refl _ _)) B |>.flip

variable {B 𝔖} in
lemma bilin_apply_apply (y : F) (x : PolarTopology B 𝔖) :
    bilin B 𝔖 y x = B (linearEquiv x) y := rfl

variable {B 𝔖} in
/-- Linear equivalence of `PolarTopology B 𝔖` with `F →ᵤ[𝔖] 𝕜`. -/
def toUniformOnFun : PolarTopology B 𝔖 →ₗ[𝕜] F →ᵤ[𝔖] 𝕜 :=
  linearEquiv.symm.arrowCongr (UniformOnFun.toFunLinearEquiv 𝔖).symm <|
    (LinearMap.ltoFun 𝕜 F 𝕜 𝕜).compRight 𝕜 B

variable {B 𝔖} in
@[simp]
lemma toUniformOnFun_apply (x : PolarTopology B 𝔖) :
    toUniformOnFun x = UniformOnFun.ofFun 𝔖 (B x) := rfl

variable {B 𝔖} in
/-- The linear map from `PolarTopology B 𝔖` into the space of continuous linear maps on
`F` (where `F` is equipped with the weak topology induced by `B.flip`) equipped with the topology
of uniform convergence on `𝔖 : Set (Set F)`. -/
noncomputable def toUniformConvergenceCLM [TopologicalSpace F] [B.flip.IsWeak] :
    PolarTopology B 𝔖 →ₗ[𝕜] F →Lᵤ[𝕜, 𝔖] 𝕜 :=
  linearEquiv.symm.arrowCongr (ContinuousLinearMap.toUniformConvergenceCLM ..) <|
    B.toCLMRight (LinearMap.IsWeak.continuous_eval B.flip)

variable [TopologicalSpace F] [B.flip.IsWeak]

variable {B 𝔖} in
@[simp]
lemma toUniformConvergenceCLM_apply_apply (x : PolarTopology B 𝔖) (y : F) :
    toUniformConvergenceCLM x y = B x y := by
  simp [toUniformConvergenceCLM]
  rfl -- gross

noncomputable instance : UniformSpace (PolarTopology B 𝔖) :=
  .comap (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) inferInstance

noncomputable instance : TopologicalSpace (PolarTopology B 𝔖) :=
  .induced (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) inferInstance

instance : IsUniformAddGroup (PolarTopology B 𝔖) := .comap _

lemma isUniformInducing_toUniformConvergenceCLM :
    IsUniformInducing (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) where
  comap_uniformity := rfl

instance : ContinuousConstSMul 𝕜 (PolarTopology B 𝔖) :=
  isUniformInducing_toUniformConvergenceCLM B 𝔖 |>.isInducing.continuousConstSMul id <| by simp

protected theorem continuousSMul [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [TopologicalSpace E]
    (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S) : ContinuousSMul 𝕜 (PolarTopology B 𝔖) := by
  have : ContinuousSMul 𝕜 (F →Lᵤ[𝕜, 𝔖] 𝕜) :=
    UniformConvergenceCLM.continuousSMul (σ := RingHom.id 𝕜) (E := F) (F := 𝕜) _ h𝔖
  apply isUniformInducing_toUniformConvergenceCLM B _ |>.isInducing.continuousSMul continuous_id <|
   by simp

lemma isUniformEmbedding_toUniformConvergenceCLM (hB : B.SeparatingLeft) :
    IsUniformEmbedding (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) where
  comap_uniformity := rfl
  injective := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hx
      apply hB
      simpa [DFunLike.ext_iff] using  hx
    · rintro rfl; exact map_zero _

--- this is a bit of a weird statement, but it also exists for `UniformConvergenceCLM`.
lemma uniformSpace_mono (𝔖 𝔗 : Set (Set F)) (h𝔖𝔗 : 𝔖 ⊆ 𝔗) :
    instUniformSpace B 𝔗 ≤ instUniformSpace B 𝔖 :=
  UniformSpace.comap_mono <| UniformConvergenceCLM.uniformSpace_mono _ _ h𝔖𝔗

--- this is a bit of a weird statement, but it also exists for `UniformConvergenceCLM`.
lemma topologicalSpace_mono (𝔖 𝔗 : Set (Set F))
    (h𝔖𝔗 : 𝔖 ⊆ 𝔗) :
    instTopologicalSpace B 𝔗 ≤ instTopologicalSpace B 𝔖 :=
  induced_mono <| UniformConvergenceCLM.topologicalSpace_mono _ _ h𝔖𝔗

lemma continuous_mono (𝔖 𝔗 : Set (Set F)) (h𝔖𝔗 : 𝔖 ⊆ 𝔗) :
    Continuous ((linearEquiv (B := B) (𝔖 := 𝔗)).trans (linearEquiv (B := B) (𝔖 := 𝔖)).symm) :=
  continuous_id_of_le (topologicalSpace_mono B 𝔖 𝔗 h𝔖𝔗)

lemma isUniformInducing_toUniformOnFun :
    IsUniformInducing (toUniformOnFun (B := B) (𝔖 := 𝔖)) := by
  convert (UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 𝔖).comp
    (isUniformInducing_toUniformConvergenceCLM B 𝔖)
  ext
  apply UniformOnFun.toFun 𝔖 |>.injective
  ext
  simp

open scoped Uniformity Topology
open UniformOnFun

variable {𝔖}

lemma hasBasis_uniformity_of_basis {ι : Type*} {p : ι → Prop} {s : ι → Set (𝕜 × 𝕜)}
    (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) (hb : (𝓤 𝕜).HasBasis p s) :
    (𝓤 (PolarTopology B 𝔖)).HasBasis
      (fun (Si : Set F × ι) ↦ Si.1 ∈ 𝔖 ∧ p Si.2)
      (fun (Si : Set F × ι) ↦
        (Prod.map toUniformOnFun toUniformOnFun) ⁻¹' (UniformOnFun.gen 𝔖 Si.1 (s Si.2))) := by
  rw [← (isUniformInducing_toUniformOnFun B 𝔖).comap_uniformity]
  exact UniformOnFun.hasBasis_uniformity_of_basis F 𝕜 𝔖 h h' hb |>.comap _

lemma hasBasis_uniformity (h : 𝔖.Nonempty) (h' : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓤 (PolarTopology B 𝔖)).HasBasis
      (fun (SV : Set F × Set (𝕜 × 𝕜)) ↦ SV.1 ∈ 𝔖 ∧ SV.2 ∈ uniformity 𝕜)
      (fun (SV : Set F × Set (𝕜 × 𝕜)) ↦
        (Prod.map toUniformOnFun toUniformOnFun) ⁻¹' (UniformOnFun.gen 𝔖 SV.1 SV.2)) := by
  rw [← (isUniformInducing_toUniformOnFun B 𝔖).comap_uniformity]
  exact UniformOnFun.hasBasis_uniformity F 𝕜 𝔖 h h' |>.comap _

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

variable (B 𝔖) in
/-- The seminorm on `PolarTopology B 𝔖` by taking for `x : E` the supremum of the values of
`B x y` over all `y ∈ s`, where `s ∈ 𝔖`. -/
noncomputable def seminorm (s : Set F) (hs : IsVonNBounded 𝕜 s) :
    Seminorm 𝕜 (PolarTopology B 𝔖) where
  toFun x := sSup ((‖B (linearEquiv x) ·‖) '' s)
  map_zero' := by simp [sSup_image']
  add_le' x₁ x₂ := by
    simp only [sSup_image']
    obtain (h | h) := isEmpty_or_nonempty s
    · simp
    rw [LinearMap.IsWeak.isVonNBounded_iff_bddAbove B.flip, LinearMap.flip_flip] at hs
    rw [ciSup_set_le_iff .of_subtype (hs (linearEquiv (x₁ + x₂)))]
    simp only [map_add, LinearMap.add_apply]
    intro y hy
    lift y to s using hy
    apply norm_add_le _ _ |>.trans <| add_le_add ?_ ?_
    · apply le_ciSup ?_ y
      simpa [Set.range_comp' (fun y : F ↦ ‖B (linearEquiv x₁) y‖)] using hs (linearEquiv x₁)
    · apply le_ciSup ?_ y
      simpa [Set.range_comp' (fun y : F ↦ ‖B (linearEquiv x₂) y‖)] using hs (linearEquiv x₂)
  neg' := by simp
  smul' := by simp [sSup_image', Real.mul_iSup_of_nonneg (norm_nonneg _)]

lemma seminorm_apply (s : Set F) (hs : IsVonNBounded 𝕜 s) (x : PolarTopology B 𝔖) :
    seminorm B 𝔖 s hs x = sSup ((‖B (linearEquiv x) ·‖) '' s) := rfl

alias _root_.Bornology.IsVonNBounded.empty := Bornology.isVonNBounded_empty

@[simp]
lemma seminorm_empty : seminorm B 𝔖 ∅ (.empty ..) = 0 := by
  ext
  simp [seminorm_apply]

lemma isLUB_seminorm {s : Set F} (hs : IsVonNBounded 𝕜 s)
    (hs_non : s.Nonempty) (x : PolarTopology B 𝔖) :
    IsLUB ((‖B (linearEquiv x) ·‖) '' s) (seminorm B 𝔖 s hs x) :=
  isLUB_csSup (hs_non.image _) (LinearMap.IsWeak.isVonNBounded_iff_bddAbove B.flip |>.mp hs _)

lemma seminorm_apply_le_iff {s : Set F} (hs : IsVonNBounded 𝕜 s)
    {r : ℝ} (hr : 0 ≤ r) (x : PolarTopology B 𝔖) :
    seminorm B 𝔖 s hs x ≤ r ↔ ∀ y ∈ s, ‖B (linearEquiv x) y‖ ≤ r := by
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simpa
  simpa [mem_upperBounds] using isLUB_le_iff (b := r) <| isLUB_seminorm hs hs_non x

lemma seminorm_apply_le {s : Set F} (hs : IsVonNBounded 𝕜 s)
    (x : PolarTopology B 𝔖) {y : WeakBilin B.flip} (hy : y ∈ s) :
    ‖B (linearEquiv x) y‖ ≤ seminorm B 𝔖 s hs x  :=
  seminorm_apply_le_iff hs (apply_nonneg _ _) x |>.mp le_rfl y hy

lemma seminorm_le_of_subset {s t : Set F} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) (hst : s ⊆ t) :
    seminorm B 𝔖 s hs ≤ seminorm B 𝔖 t ht := by
  intro x
  simp only
  rw [seminorm_apply_le_iff hs (apply_nonneg _ _)]
  exact fun y hy ↦ seminorm_apply_le ht x (hst hy)

lemma seminorm_union {s t : Set F} (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    seminorm B 𝔖 (s ∪ t) (hs.union ht) = seminorm B 𝔖 s hs ⊔ seminorm B 𝔖 t ht := by
  ext
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simp
  obtain (rfl | ht_non) := t.eq_empty_or_nonempty; · simp
  exact isLUB_seminorm (hs.union ht) hs_non.inl _ |>.unique <|
    (Set.image_union ..) ▸ (isLUB_seminorm hs hs_non _).union (isLUB_seminorm ht ht_non _)

lemma seminorm_finite_sUnion {s : Set (Set F)} (hs : s.Finite)
   (hsbdd : ∀ t ∈ s, Bornology.IsVonNBounded 𝕜 t) :
    seminorm B 𝔖 (⋃₀ s) ((isVonNBounded_sUnion hs).mpr hsbdd) =
      iSup (fun (i : {t // t ∈ s}) ↦ seminorm B 𝔖 i.1 (hsbdd i.1 i.2)) := by
  revert hsbdd
  refine Set.Finite.induction_on s hs ?_ ?_
  · simp only [mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
      sUnion_empty, forall_true_left, mem_empty_iff_false]
    ext
    rw [Seminorm.iSup_apply (by simp)]
    simp [Real.iSup_of_isEmpty]
  · intro p hp hnp hfin himp hyp
    simp only [sUnion_insert]
    rw [Set.forall_mem_insert, seminorm_union hyp.1 ((isVonNBounded_sUnion hfin).mpr hyp.2)] at *
    obtain (h_empty | h_nonempty) := isEmpty_or_nonempty hp
    · have : IsEmpty { t // t ∈ hp} := Function.isEmpty id
      simp only [isEmpty_coe_sort] at h_empty
      simp only [h_empty, sUnion_empty, iSup, range_insert]
      simp only [range]
      ext; simp
    · simp only [iSup, range_insert]
      rw [csSup_insert]
      · exact
        Seminorm.ext_iff.mpr
          (congrFun (congrArg DFunLike.coe (congrArg (max (seminorm B 𝔖 p hyp.1)) <| himp hyp.2)))
      · have := finite_coe_iff.mpr hfin
        apply Finite.bddAbove_range
      exact range_nonempty_iff_nonempty.mpr h_nonempty

lemma continuous_seminorm (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
      (s : Set F) (hs_mem : s ∈ 𝔖) (hs : IsVonNBounded 𝕜 s) :
    Continuous (seminorm B 𝔖 s hs) := by
  have := UniformConvergenceCLM.hasBasis_nhds_zero_of_basis'
    (RingHom.id 𝕜) 𝕜 𝔖 h𝔖_non h𝔖_dir Metric.nhds_basis_closedBall
    |>.comap (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖))
  apply Seminorm.continuous_of_continuousAt_zero
  rw [← map_zero (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)), ← nhds_induced] at this
  simp only [Metric.mem_closedBall, dist_zero_right] at this
  rw [ContinuousAt, this.tendsto_iff Metric.nhds_basis_closedBall]
  intro ε hε
  simp only [preimage_setOf_eq, toUniformConvergenceCLM_apply_apply, mem_setOf_eq,
    map_zero, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  simp_rw [abs_of_nonneg (apply_nonneg _ _)]
  refine ⟨(s, ε), ⟨hs_mem, hε⟩, fun x hx ↦ ?_⟩
  simpa [seminorm_apply_le_iff hs hε.le x, pairing_apply]

open TopologicalSpace

variable (B 𝔖) in
/-- The natural `SeminormFamily` associated to `PolarTopology B 𝔖`. -/
noncomputable def seminormFamily (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    SeminormFamily 𝕜 (PolarTopology B 𝔖) 𝔖 :=
  fun s ↦ seminorm B 𝔖 s.1 (h𝔖 _ s.2)

lemma seminormFamily_apply (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) (s : 𝔖) :
    seminormFamily B 𝔖 h𝔖 s = seminorm B 𝔖 s.1 (h𝔖 _ s.2) := rfl

lemma directed_seminormFamily (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖) :
    Directed (· ≤ ·) (seminormFamily B 𝔖 h𝔖) := by
  intro s t
  obtain ⟨u, hu', hu⟩ := h𝔖_dir _ s.2 _ t.2
  lift u to 𝔖 using hu'
  use u
  exact ⟨seminorm_le_of_subset (h𝔖 _ s.2) (h𝔖 _ u.2) hu.1,
    seminorm_le_of_subset (h𝔖 _ t.2) (h𝔖 _ u.2) hu.2⟩

variable (B 𝔖) in
lemma withSeminorms (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
    (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    WithSeminorms (seminormFamily B 𝔖 h𝔖) := by
  apply (seminormFamily B 𝔖 h𝔖).withSeminorms_of_hasBasis
  have := UniformConvergenceCLM.hasBasis_nhds_zero_of_basis'
    (RingHom.id 𝕜) 𝕜 𝔖 h𝔖_non h𝔖_dir Metric.nhds_basis_ball
    |>.comap (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖))
  rw [← map_zero (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)), ← nhds_induced] at this
  simp only [Metric.mem_ball, dist_zero_right] at this
  apply this.to_hasBasis' ?_ ?_
  · simp only [id_eq, preimage_setOf_eq, toUniformConvergenceCLM_apply_apply, and_imp, Prod.forall]
    intro s ε hs hε
    simp only [SeminormFamily.basisSets, mem_iUnion, mem_singleton_iff, exists_prop, ↓existsAndEq,
      and_true]
    change ∃ t, ∃ δ > 0, _
    lift s to 𝔖 using hs
    use {s}, ε, hε
    intro x
    simp only [Finset.sup_singleton, seminormFamily_apply, Seminorm.ball_zero_eq_preimage_ball,
      mem_preimage, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs, mem_setOf_eq]
    intro hx y hy
    replace hx := le_abs_self _ |>.trans_lt hx
    obtain (hs | hs) := s.1.eq_empty_or_nonempty; · simp_all
    have := isLUB_seminorm (h𝔖 _ s.2) hs x |>.1 ⟨y, hy, rfl⟩
    exact isLUB_seminorm (h𝔖 _ s.2) hs x |>.1 ⟨y, hy, rfl⟩ |>.trans_lt hx
  · apply SeminormFamily.basisSets_mem_nhds _ fun s ↦ ?_
    exact continuous_seminorm h𝔖_non h𝔖_dir s.1 s.2 (h𝔖 _ s.2)

lemma unitClosedBall_seminorm_eq_polar {s : Set F} (hs : IsVonNBounded 𝕜 s) :
    (seminorm B 𝔖 s hs).closedBall 0 1 = (bilin B 𝔖).polar s := by
  ext y
  simpa [LinearMap.polar_mem_iff] using seminorm_apply_le_iff hs zero_le_one y

lemma polar_mem_nhds (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
    (s : Set F) (hs_mem : s ∈ 𝔖) (hs : IsVonNBounded 𝕜 s) :
    (bilin B 𝔖).polar s ∈ 𝓝 (0 : PolarTopology B 𝔖) := by
  have h_cont := continuous_seminorm (B := B) h𝔖_non h𝔖_dir s hs_mem hs |>.tendsto 0
  have h_mem := map_zero (seminorm B 𝔖 s hs) ▸ Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one
  simpa [← Seminorm.closedBall_zero_eq_preimage_closedBall, unitClosedBall_seminorm_eq_polar]
    using h_cont h_mem

open scoped Pointwise NNReal in
lemma hasBasis_nhds_zero_polar [Module ℝ F] [IsScalarTower ℝ 𝕜 F]
    (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
    (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s)
    (h𝔖_scale : ∀ c > (0 : ℝ), ∀ s ∈ 𝔖, ∃ t ∈ 𝔖, c • s ⊆ t) :
    (𝓝 (0 : PolarTopology B 𝔖)).HasBasis (· ∈ 𝔖) (bilin B 𝔖).polar := by
  have _ := h𝔖_non.to_subtype
  have := withSeminorms B 𝔖 h𝔖_non h𝔖_dir h𝔖 |>.hasBasis_zero_closedBall_of_directed <|
    directed_seminormFamily h𝔖 h𝔖_dir
  apply this.to_hasBasis' ?_ fun s hs ↦ polar_mem_nhds h𝔖_non h𝔖_dir s hs (h𝔖 s hs)
  rintro ⟨s, r⟩ (hr : 0 < r)
  obtain ⟨t, ht, hrst⟩ := h𝔖_scale r⁻¹ (by positivity) s.1 s.2
  refine ⟨t, ht, ?_⟩
  apply Set.Subset.trans <| LinearMap.polar_antitone (bilin B 𝔖) hrst
  rw [← smul_one_smul 𝕜]
  rw [LinearMap.polar_smul _ _ (r⁻¹ • 1) (by simpa using hr.ne')]
  lift r to ℝ≥0 using hr.le
  simp only [smul_inv₀, inv_inv, inv_one, ← NNReal.smul_def]
  rw [← unitClosedBall_seminorm_eq_polar (h𝔖 _ s.2)]
  rintro - ⟨x, hx, rfl⟩
  simp only [Seminorm.mem_closedBall, sub_zero, seminormFamily_apply] at hx ⊢
  grw [map_smul_eq_mul, hx]
  simp [NNReal.smul_def]

open scoped ComplexOrder

theorem locallyConvexSpace [Module ℝ E] [h : IsScalarTower ℝ 𝕜 E] (h𝔖_non : 𝔖.Nonempty)
    (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    LocallyConvexSpace ℝ (PolarTopology B 𝔖) :=
  (withSeminorms B 𝔖 h𝔖_non h𝔖_dir h𝔖 ).toLocallyConvexSpace

-- Question: Should we first map these through `linearEquiv.symm`, and then `(bilin B 𝔖).polar`?
-- It might make it easier to apply the bipolar theorem later.
lemma isVonNBounded_nhdsPolars [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [hB : B.IsCompatibleDual] (s : Set F) (hs : s ∈ B.nhdsPolars) :
    IsVonNBounded 𝕜 s := by
  obtain ⟨s, (hs : s ∈ 𝓝 0), rfl⟩ := hs
  exact hB.isVonNBounded_polar _ hs

variable (B) in
lemma continuous_seminorm_comp [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [B.IsCompatibleDual] {s : Set E} (hs1 : s ∈ 𝓝 0) :
    Continuous
      (seminorm B B.nhdsPolars (B.polar s) (isVonNBounded_nhdsPolars _ ⟨s, hs1, rfl⟩) |>.comp <|
        linearEquiv.symm.toLinearMap) := by
  apply Seminorm.continuous_of_continuousAt_zero
  refine Seminorm.continuousAt_zero' (r := 1) <| mem_of_superset hs1 fun x hx ↦ ?_
  simp only [Seminorm.mem_closedBall, sub_zero, Seminorm.comp_apply, LinearEquiv.coe_coe,
    seminorm_apply, LinearEquiv.apply_symm_apply]
  apply csSup_le (B.polar_nonempty s |>.image _)
  rintro - ⟨y, hy, rfl⟩
  exact B.polar_mem s y hy x hx

open LinearMap WithSeminorms

/- I've changed the following docstring back to what it was, as I previously replaced
 `B.flip` by `B` since the statement of the def has `B.IsCompatibleDual` and not
 `B.flip.IsCompatibleDual`, but I want to clarify why we originally had the docstring like
 this. I mean, the math doesn't lie, but I'm concerned that there was a good reason before
 for us to have this as `B.flip`. Will keep thinking about it, but wanted to flag it here. -/

/-- The continuous linear equivalence between `E` satisfiying `B.flip.IsCompatibleDual` and
`PolarTopology B (nhdsPolars B)`. -/
def polarTopologyNhdsPolars [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [hLCS : LocallyConvexSpace 𝕜 E]
    [hB : B.IsCompatibleDual] :
    PolarTopology B (nhdsPolars B) ≃L[𝕜] E where
  toLinearEquiv := linearEquiv (B := B) (𝔖 := nhdsPolars B)
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    letI f := (PolarTopology.linearEquiv (B := B) (𝔖 := nhdsPolars B))
    letI B₂ := bilin B (nhdsPolars B)
    apply continuous_of_tendsto_nhds_zero
    rw [Filter.HasBasis.tendsto_right_iff (LocallyConvexSpace.absConvex_closed_basis_zero 𝕜 E)]
    rintro u ⟨hu_nhd, hu_ac, hu_cl⟩
    let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
    let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
    have hR : LocallyConvexSpace ℝ E := LocallyConvexSpace.to_real 𝕜 E hLCS
    have : B₂.polar (B.polar u) = f ⁻¹' u := by
      nth_rw 2 [← closedAbsConvexHull_eq_self hu_ac hu_cl]
      rw [← IsCompatibleDual.flip_polar_polar (Filter.nonempty_of_mem hu_nhd) (B := B)]
      ext; congr!
    simp only [id_eq]
    have foo := polar_mem_nhds (B := B) (𝔖 := nhdsPolars B) nonempty_nhdsPolars
      directedOn_nhdsPolars (B.polar u) ⟨u, hu_nhd, rfl⟩ (hB.isVonNBounded_polar _ hu_nhd)
    filter_upwards [foo] with x hx using show x ∈ f ⁻¹' u from this ▸ hx
  continuous_invFun := by
    simp only [LinearEquiv.invFun_eq_symm]
    apply withSeminorms B (nhdsPolars B) nonempty_nhdsPolars directedOn_nhdsPolars
      isVonNBounded_nhdsPolars |>.continuous_of_continuous_comp _
    rintro ⟨-, ⟨s, (hs : s ∈ 𝓝 0), rfl⟩⟩
    exact continuous_seminorm_comp B hs

end PolarTopology

end PolarTopology
