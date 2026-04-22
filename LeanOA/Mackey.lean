import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.Topology.Sets.Compacts
import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar
import LeanOA.Mathlib.Analysis.LocallyConvex.Bounded
import LeanOA.Mathlib.Analysis.LocallyConvex.IsCompatible
import LeanOA.Mathlib.Analysis.LocallyConvex.WeakBilin
import LeanOA.Mathlib.Analysis.LocallyConvex.WithSeminorms
import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
import LeanOA.Mathlib.Analysis.Normed.Group.Uniform
import LeanOA.Mathlib.Topology.Algebra.UniformConvergence

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

-- the version in Mathlib has some small defeq abuse. It uses `f : E →SL[σ] F`
open scoped UniformConvergenceCLM UniformConvergence in
lemma UniformConvergenceCLM.hasBasis_nhds_zero_of_basis'
    {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type*} (F : Type*)
    [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜₂ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] {ι : Type*} (𝔖 : Set (Set E))
    (h𝔖₁ : 𝔖.Nonempty) (h𝔖₂ : DirectedOn (fun (x1 x2 : Set E) => x1 ⊆ x2) 𝔖) {p : ι → Prop}
    {b : ι → Set F} (h : (nhds 0).HasBasis p b) :
    (nhds 0).HasBasis (fun (Si : Set E × ι) => Si.1 ∈ 𝔖 ∧ p Si.2) fun (Si : Set E × ι) =>
      {f : E →SLᵤ[σ, 𝔖] F | ∀ x ∈ Si.1, f x ∈ b Si.2} :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F 𝔖 h𝔖₁ h𝔖₂ h


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

end LinearMap

section Banach_Alaoglu

open WeakBilin Topology in
theorem IsCompatible.isCompact_polar {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [ProperSpace 𝕜] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible]
    {s : Set E} (s_nhds : s ∈ 𝓝 0) :
    IsCompact ((pairing B.flip).flip.polar s) := by
  have := WeakDual.isCompact_polar' 𝕜 s_nhds |>.image h.weakDualCLE.symm.continuous
  rw [ContinuousLinearEquiv.image_eq_preimage_symm] at this
  exact this

end Banach_Alaoglu

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
def PolarTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip))) := E
deriving AddCommGroup, Module 𝕜

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (𝔖 : Set (Set (WeakBilin B.flip))) :
    Module 𝕝 (PolarTopology B 𝔖) :=
  ‹Module 𝕝 E›

instance {𝕝 : Type*} [CommRing 𝕝] [Module 𝕝 E] [SMul 𝕝 𝕜] [IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip))) :
    IsScalarTower 𝕝 𝕜 (PolarTopology B 𝔖) :=
  ‹IsScalarTower 𝕝 𝕜 E›

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set (WeakBilin B.flip)))

namespace PolarTopology

open UniformOnFun Topology WeakBilin

open scoped UniformConvergenceCLM

variable {B 𝔖} in
/-- The canonical equivalence between `PolarTopology B 𝔖` and `E`. -/
def linearEquiv : PolarTopology B 𝔖 ≃ₗ[𝕜] E := .refl _ _

/-- Upgrade a bilinear map `B : E →ₗ[𝕜] F →ₗ[𝕜] → 𝕜` to a linear map into continuous linear maps
`B : E →ₗ[𝕜] F →L[𝕜] → 𝕜` (this can be generalized a lot; no need for scalars, also we can
semilinearize). -/
noncomputable def _root_.LinearMap.toCLMRight [TopologicalSpace F] (hB : ∀ x, Continuous (B x)) :
    E →ₗ[𝕜] F →L[𝕜] 𝕜 :=
  letI e : (F →L[𝕜] 𝕜) ≃ₗ[𝕜] (ContinuousLinearMap.coeLM 𝕜 (M := F) (N₃ := 𝕜) (R := 𝕜)).range :=
    .ofInjective (ContinuousLinearMap.coeLM 𝕜) fun _ _ ↦ by simp [DFunLike.ext_iff]
  letI B' : E →ₗ[𝕜] (ContinuousLinearMap.coeLM 𝕜 (M := F) (N₃ := 𝕜) (R := 𝕜)).range :=
    B.codRestrict  _ (fun x ↦ ⟨⟨B x, hB x⟩, rfl⟩)
  (LinearEquiv.refl _ _).arrowCongr e.symm B'

@[simp]
lemma _root_.LinearMap.coeLM_toCLMRight_apply [TopologicalSpace F] (hB : ∀ x, Continuous (B x))
    (x : E) : (B.toCLMRight hB x).coeLM 𝕜 = B x := by
  simp [LinearMap.toCLMRight]

@[simp]
lemma _root_.LinearMap.coe_toCLMRight [TopologicalSpace F] (hB : ∀ x, Continuous (B x))
    (x : E) : ⇑(B.toCLMRight hB x) = B x := by
  congrm($(B.coeLM_toCLMRight_apply hB x))

variable {B 𝔖} in
/-- The linear map from `PolarTopology B 𝔖` into the space of continuous linear maps on
`F` (where `F` is equipped with the weak topology induced by `B.flip`) equipped with the topology
of uniform convergence on `𝔖 : Set (Set (WeakBilin B.flip))`. -/
noncomputable def toUniformConvergenceCLM :
    PolarTopology B 𝔖 →ₗ[𝕜] WeakBilin B.flip →Lᵤ[𝕜, 𝔖] 𝕜 :=
  linearEquiv.symm.arrowCongr (ContinuousLinearMap.toUniformConvergenceCLM ..) <|
    (pairing B.flip).flip.toCLMRight (eval_continuous B.flip)

variable {B 𝔖} in
@[simp]
lemma toUniformConvergenceCLM_apply_apply (x : PolarTopology B 𝔖) (y : WeakBilin B.flip) :
    toUniformConvergenceCLM x y = B x y := by
  simp [toUniformConvergenceCLM]
  rfl -- gross

noncomputable instance : UniformSpace (PolarTopology B 𝔖) :=
  .comap (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) inferInstance

instance : IsUniformAddGroup (PolarTopology B 𝔖) := .comap _

lemma isUniformInducing_toUniformConvergenceCLM :
    IsUniformInducing (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)) where
  comap_uniformity := rfl

instance : ContinuousConstSMul 𝕜 (PolarTopology B 𝔖) :=
  isUniformInducing_toUniformConvergenceCLM B 𝔖 |>.isInducing.continuousConstSMul id <| by simp

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

variable {B 𝔖} in
def toUniformOnFun : PolarTopology B 𝔖 →ₗ[𝕜] F →ᵤ[𝔖] 𝕜 :=
  linearEquiv.symm.arrowCongr (UniformOnFun.toFunLinearEquiv 𝔖).symm <|
    (LinearMap.ltoFun 𝕜 F 𝕜 𝕜).compRight 𝕜 B

variable {B 𝔖} in
@[simp]
lemma toUniformOnFun_apply (x : PolarTopology B 𝔖) :
    toUniformOnFun x = UniformOnFun.ofFun 𝔖 (B x) := by
  rfl

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

--- do we still need this?
lemma isBounded_pairing_flip_flip_of_isCompact (s : Set (WeakBilin B.flip)) (hs : IsCompact s)
    (x : E) : IsBounded ((pairing B.flip).flip x '' s) :=
  hs.image (eval_continuous B.flip x) |>.isBounded

variable (B 𝔖) in
/-- The seminorm on `PolarTopology B 𝔖` by taking for `x : E` the supremum of the values of
`B x y` over all `y ∈ s`, where `s ∈ 𝔖`. -/
noncomputable def seminorm (s : Set (WeakBilin B.flip)) (hs : IsVonNBounded 𝕜 s) :
    Seminorm 𝕜 (PolarTopology B 𝔖) where
  toFun x := sSup ((‖(pairing B.flip).flip (linearEquiv x) ·‖) '' s)
  map_zero' := by simp [sSup_image']
  add_le' x₁ x₂ := by
    simp only [sSup_image']
    obtain (h | h) := isEmpty_or_nonempty s
    · simp
    rw [WeakBilin.isVonNBounded_iff_bddAbove] at hs
    rw [ciSup_set_le_iff .of_subtype (hs (linearEquiv (x₁ + x₂)))]
    simp only [map_add, LinearMap.add_apply]
    intro y hy
    lift y to s using hy
    apply norm_add_le _ _ |>.trans <| add_le_add ?_ ?_
    · apply le_ciSup ?_ y
      simpa [Set.range_comp' (fun y : WeakBilin B.flip ↦ ‖pairing B.flip y (linearEquiv x₁)‖)]
        using hs (linearEquiv x₁)
    · apply le_ciSup ?_ y
      simpa [Set.range_comp' (fun y : WeakBilin B.flip ↦ ‖pairing B.flip y (linearEquiv x₂)‖)]
        using hs (linearEquiv x₂)
  neg' := by simp
  smul' := by simp [sSup_image', Real.mul_iSup_of_nonneg (norm_nonneg _)]

lemma seminorm_apply (s : Set (WeakBilin B.flip)) (hs : IsVonNBounded 𝕜 s) (x : PolarTopology B 𝔖) :
    seminorm B 𝔖 s hs x = sSup ((‖(pairing B.flip).flip (linearEquiv x) ·‖) '' s) := by
  rfl

alias _root_.Bornology.IsVonNBounded.empty := Bornology.isVonNBounded_empty

@[simp]
lemma seminorm_empty : seminorm B 𝔖 ∅ (.empty ..) = 0 := by
  ext
  simp [seminorm_apply]

lemma _root_.Real.sSup_image_nonneg {α : Type*} {f : α → ℝ} {s : Set α} (h : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ sSup (f '' s) := by
  apply Real.sSup_nonneg
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

lemma isLUB_seminorm {s : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
    (hs_non : s.Nonempty) (x : PolarTopology B 𝔖) :
    IsLUB ((‖(pairing B.flip).flip (linearEquiv x) ·‖) '' s) (seminorm B 𝔖 s hs x) :=
  isLUB_csSup (hs_non.image _) (WeakBilin.isVonNBounded_iff_bddAbove.mp hs _)

lemma seminorm_apply_le_iff {s : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
    {r : ℝ} (hr : 0 ≤ r) (x : PolarTopology B 𝔖) :
    seminorm B 𝔖 s hs x ≤ r ↔ ∀ y ∈ s, ‖(pairing B.flip).flip (linearEquiv x) y‖ ≤ r := by
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simpa
  simpa [mem_upperBounds] using isLUB_le_iff (b := r) <| isLUB_seminorm hs hs_non x

lemma seminorm_apply_le {s : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
    (x : PolarTopology B 𝔖) {y : WeakBilin B.flip} (hy : y ∈ s) :
    ‖(pairing B.flip).flip (linearEquiv x) y‖ ≤ seminorm B 𝔖 s hs x  :=
  seminorm_apply_le_iff hs (apply_nonneg _ _) x |>.mp le_rfl y hy

lemma seminorm_le_of_subset {s t : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) (hst : s ⊆ t) :
    seminorm B 𝔖 s hs ≤ seminorm B 𝔖 t ht := by
  intro x
  simp only
  rw [seminorm_apply_le_iff hs (apply_nonneg _ _)]
  exact fun y hy ↦ seminorm_apply_le ht x (hst hy)

lemma seminorm_union {s t : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
      (ht : IsVonNBounded 𝕜 t) :
    seminorm B 𝔖 (s ∪ t) (hs.union ht) = seminorm B 𝔖 s hs ⊔ seminorm B 𝔖 t ht := by
  ext
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simp
  obtain (rfl | ht_non) := t.eq_empty_or_nonempty; · simp
  exact isLUB_seminorm (hs.union ht) hs_non.inl _ |>.unique <|
    (Set.image_union ..) ▸ (isLUB_seminorm hs hs_non _).union (isLUB_seminorm ht ht_non _)

lemma seminorm_finite_sUnion {s : Set (Set (WeakBilin B.flip))} (hs : s.Finite)
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
      (s : Set (WeakBilin B.flip)) (hs_mem : s ∈ 𝔖) (hs : IsVonNBounded 𝕜 s) :
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
noncomputable def seminormFamily (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    SeminormFamily 𝕜 (PolarTopology B 𝔖) 𝔖 :=
  fun s ↦ seminorm B 𝔖 s.1 (h𝔖 _ s.2)

lemma seminormFamily_apply (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) (s : 𝔖) :
    seminormFamily B 𝔖 h𝔖 s = seminorm B 𝔖 s.1 (h𝔖 _ s.2) := by
  rfl

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

variable (B 𝔖) in
abbrev bilin : WeakBilin B.flip →ₗ[𝕜] PolarTopology B 𝔖 →ₗ[𝕜] 𝕜 :=
  linearEquiv.symm.arrowCongr (.refl _ _) (pairing B.flip).flip |>.flip

lemma bilin_apply_apply (y : WeakBilin B.flip) (x : PolarTopology B 𝔖) :
    bilin B 𝔖 y x = B (linearEquiv x) (WeakBilin.linearEquiv 𝕜 B.flip y) := by
  rfl

lemma unitClosedBall_seminorm_eq_polar {s : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s) :
    (seminorm B 𝔖 s hs).closedBall 0 1 = (bilin B 𝔖).polar s := by
  ext y
  simpa [LinearMap.polar_mem_iff] using seminorm_apply_le_iff hs zero_le_one y

lemma polar_mem_nhds (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
    (s : Set (WeakBilin B.flip)) (hs_mem : s ∈ 𝔖) (hs : IsVonNBounded 𝕜 s) :
    (bilin B 𝔖).polar s ∈ 𝓝 (0 : PolarTopology B 𝔖) := by
  have h_cont := continuous_seminorm h𝔖_non h𝔖_dir s hs_mem hs |>.tendsto 0
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

instance [Module ℝ E] [h : IsScalarTower ℝ 𝕜 E] (h𝔖_non : 𝔖.Nonempty)
    (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    LocallyConvexSpace ℝ (PolarTopology B 𝔖) :=
  (withSeminorms B 𝔖 h𝔖_non h𝔖_dir h𝔖 ).toLocallyConvexSpace

-- Question: Should we first map these through `linearEquiv.symm`, and then `(bilin B 𝔖).polar`?
-- It might make it easier to apply the bipolar theorem later.
variable (B) in
/-- The collection of polars of neighborhoods of zero. -/
def nhdsPolars [TopologicalSpace E] : Set (Set (WeakBilin B.flip)) :=
  (pairing B.flip).flip.polar '' (𝓝 0).sets

lemma nonempty_nhdsPolars [TopologicalSpace E] : (nhdsPolars B).Nonempty :=
  Set.Nonempty.image _ ⟨univ, univ_mem⟩

lemma directedOn_nhdsPolars [TopologicalSpace E] : DirectedOn (· ⊆ ·) (nhdsPolars B) := by
  rintro - ⟨s₁, (hs₁ : s₁ ∈ 𝓝 0), rfl⟩ - ⟨s₂, (hs₂ : s₂ ∈ 𝓝 0), rfl⟩
  refine ⟨_, ⟨s₁ ∩ s₂, inter_mem hs₁ hs₂, rfl⟩, ?_, ?_⟩
  all_goals exact LinearMap.polar_antitone _ <| by simp

lemma nhdsPolars_mem_iff [TopologicalSpace E] {s : Set F} :
    s ∈ nhdsPolars B ↔ ∃ u ∈ 𝓝 0, (pairing B.flip).flip.polar u = s :=
  Eq.to_iff rfl

lemma polar_mem_nhdsPolars [TopologicalSpace E] {s : Set E} (hs : s ∈ 𝓝 0) :
    (pairing B.flip).flip.polar s ∈ nhdsPolars B :=
  ⟨s, hs, rfl⟩

open scoped Pointwise in
lemma scale_nhdsPolars [TopologicalSpace E] [ContinuousConstSMul 𝕜 E]
    [Module ℝ F] [IsScalarTower ℝ 𝕜 F] {c : ℝ} (hc : 0 < c)
    {s : Set (WeakBilin B.flip)} (hs : s ∈ nhdsPolars B) :
    c • s ∈ nhdsPolars B := by
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  have _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  have _ : ContinuousConstSMul ℝ E := sorry -- this should be a lemma in Mathlib, but it's missing.
  obtain ⟨s, (hs : s ∈ 𝓝 0), rfl⟩ := hs

  sorry

-- sorry
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

open LinearMap WithSeminorms

instance [TopologicalSpace E] [B.IsCompatible] :
    LinearMap.IsCompatible (pairing B.flip).flip := by
  let e := WeakBilin.linearEquiv 𝕜 B.flip ≪≫ₗ LinearMap.IsCompatible.equiv B
  exact e.isCompatible _ rfl

/-- The continuous linear equivalence between `E` satisfiying `B.flip.IsCompatible` and
`PolarTopology B (nhdsPolars B)`. -/
def polarTopologyNhdsPolars [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E]
    [B.IsCompatible] :
    PolarTopology B (nhdsPolars B) ≃L[𝕜] E where
  toLinearEquiv := linearEquiv (B := B) (𝔖 := nhdsPolars B)
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    sorry
  continuous_invFun := by sorry
    -- have : LinearMap.IsCompatible (pairing B.flip).flip := inferInstance
    -- simp only [LinearEquiv.invFun_eq_symm]
    -- apply (withSeminorms B (nhdsPolars B)).continuous_of_continuous_comp _
    -- rintro ⟨-, ⟨s, (hs : s ∈ 𝓝 0), rfl⟩⟩
    -- exact Seminorm.continuous_of_continuousAt_zero <| continuousAt_zero_seminorm B hs

end PolarTopology

end PolarTopology
