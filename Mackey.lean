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

lemma WeakBilin.pairing_apply {𝕜 E F : Type*} [CommSemiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x : WeakBilin B) :
    pairing B x = B (linearEquiv 𝕜 B x) :=
  rfl

lemma WithSeminorms.hasBasis_zero_closedBall
    {𝕜 E ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    (nhds 0).HasBasis (fun (sr : Finset ι × ℝ) => 0 < sr.2)
      fun (sr : Finset ι × ℝ) => (sr.1.sup p).closedBall 0 sr.2 := by
  apply hp.hasBasis_ball.to_hasBasis ?_
    fun i hi ↦ ⟨i, hi, Seminorm.ball_subset_closedBall (i.1.sup p) 0 i.2⟩
  refine fun i hi ↦ ⟨(i.1, i.2 / 2), by positivity, ?_⟩
  rw [Seminorm.closedBall_zero_eq_preimage_closedBall, Seminorm.ball_zero_eq_preimage_ball]
  gcongr
  exact Metric.closedBall_subset_ball (half_lt_self hi)

lemma WithSeminorms.hasBasis_zero_closedBall_of_directed
    {𝕜 E ι : Type*} [Nonempty ι] [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (hp_dir : Directed (· ≤ ·) p) :
    (nhds 0).HasBasis (fun (ir : ι × ℝ) => 0 < ir.2)
      fun (ir : ι × ℝ) => (p ir.1).closedBall 0 ir.2 := by
  apply hp.hasBasis_zero_closedBall.to_hasBasis ?_ ?_
  · rintro ⟨s, r⟩ (hr : 0 < r)
    classical
    obtain ⟨-, ⟨i, rfl⟩, hi⟩ := (s.image p).sup_le_of_le_directed _
        (Set.range_nonempty _) hp_dir.directedOn_range <| by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨_, ⟨i, rfl⟩, le_rfl⟩
    have : s.sup p ≤ p i := Finset.sup_le <| by simpa using hi
    exact ⟨(i, r), hr, Seminorm.closedBall_antitone this⟩
  · rintro ⟨i, r⟩ (hr : 0 < r)
    refine ⟨({i}, r), hr, by simp⟩

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

namespace WeakBilin

lemma isInducing {𝕜 E F : Type*} [TopologicalSpace 𝕜] [CommSemiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Topology.IsInducing (fun x i ↦ pairing B x i) where
  eq_induced := rfl

end WeakBilin

namespace Bornology

@[to_additive isBounded_norm_iff]
lemma isBounded_norm_iff' {E : Type*} [SeminormedGroup E] {s : Set E} :
    IsBounded ((‖·‖) '' s) ↔ IsBounded s := by
  refine ⟨fun hs ↦ ?_, lipschitzWith_one_norm'.isBounded_image⟩
  rw [isBounded_iff_forall_norm_le']
  rw [isBounded_iff_bddBelow_bddAbove] at hs
  simpa [BddAbove, upperBounds] using hs.2

alias ⟨IsBounded.of_norm', IsBounded.norm'⟩ := isBounded_norm_iff'

attribute [to_additive IsBounded.of_norm] IsBounded.of_norm'
attribute [to_additive IsBounded.norm] IsBounded.norm'

variable {𝕜 E ι : Type*} {Eι : ι → Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    [∀ i, AddCommGroup (Eι i)] [∀ i, Module 𝕜 (Eι i)]
    [∀ i, TopologicalSpace (Eι i)]
    (f : (i : ι) → E →ₗ[𝕜] Eι i)

open scoped Pointwise in
lemma isVonNBounded_iff_of_iInf_induced
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    @IsVonNBounded 𝕜 E _ _ _ (⨅ i, .induced (f i) inferInstance) s := by
  simp_rw [isVonNBounded_iff] at hs ⊢
  intro v hv
  rw [nhds_iInf, Filter.mem_iInf] at hv
  obtain ⟨I, hI_fin, u, hu, rfl⟩ := hv
  have := hI_fin.to_subtype
  rw [absorbs_iInter]
  simp only [nhds_induced, map_zero, Filter.mem_comap] at hu
  intro i
  obtain ⟨t, ht, htu⟩ := hu i
  specialize hs i t ht
  filter_upwards [hs, isBounded_singleton (x := 0) |>.compl] with c hc hc₀
  -- alternate proof insteead of hte `calc` block.
  -- grw [Set.subset_preimage_image (f i) s, hc, IsUnit.mk0 c hc₀ |>.preimage_smul_set .., htu]
  calc
    s ⊆ f i ⁻¹' (f i '' s) := Set.subset_preimage_image ..
    _ ⊆ f i ⁻¹' (c • t) := by gcongr
    _ = c • f i ⁻¹' t := IsUnit.mk0 c hc₀ |>.preimage_smul_set ..
    _ ⊆ c • u i := by gcongr

open scoped Pointwise in
lemma isVonNBounded_iff_of_iInf_induced'
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    @IsVonNBounded 𝕜 E _ _ _ (.induced (fun x i ↦  f i x) Pi.topologicalSpace) s := by
  convert isVonNBounded_iff_of_iInf_induced f s hs
  exact induced_to_pi fun x i ↦ (f i) x

lemma _root_.Topology.IsInducing.isVonNBounded [TopologicalSpace E]
    (hf : Topology.IsInducing (fun x i ↦ f i x))
    (s : Set E) (hs : ∀ i, IsVonNBounded 𝕜 (f i '' s)) :
    IsVonNBounded 𝕜 s :=
  hf.eq_induced ▸ isVonNBounded_iff_of_iInf_induced' f s hs

lemma _root_.Topology.IsInducing.isVonNBounded_iff [TopologicalSpace E]
    (hf : Topology.IsInducing (fun x i ↦ f i x))
    (s : Set E) :
    IsVonNBounded 𝕜 s ↔ ∀ i, IsVonNBounded 𝕜 (f i '' s) := by
  -- this is stupid because the `CanLift` instance for linear maps to continuous
  -- linear maps assumes finite dimensionality.
  have (i : ι) : Continuous (f i) := by
    have := hf.continuous
    rw [continuous_pi_iff] at this
    exact this i
  let F : (i : ι) → E →L[𝕜] Eι i := fun i ↦ ⟨f i, this i⟩
  have (i : ι) : ⇑(F i) = f i := by simp [F]
  simp_rw [← this]
  exact ⟨fun hs i ↦ hs.image _, hf.isVonNBounded f s⟩

end Bornology

namespace LinearMap

open scoped Pointwise

section NormedField

variable {𝕜 E F F' : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F'] [Module 𝕜 F']
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

lemma polar_smul (s : Set E) (c : 𝕜) (hc : c ≠ 0) : B.polar (c • s) = c⁻¹ • B.polar s := by
  ext x
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  simp [polar, Set.mem_smul_set]
  simp [← Units.smul_def, smul_eq_iff_eq_inv_smul, ← Units.val_inv_eq_inv_val]
  simp [Units.smul_def]
  -- clean up later.

lemma smul_mem_polar_iff (s : Set E) (c : 𝕜) (hc : c ≠ 0) (y : F) :
    c • y ∈ B.polar s ↔ ∀ x ∈ s, ‖B x y‖ ≤ ‖c‖⁻¹ := by
  simp only [polar_mem_iff, map_smul, smul_eq_mul, norm_mul]
  congr! 2 with x hx
  rw [← inv_inv ‖c‖, inv_mul_le_one₀ (by simpa), inv_inv]

open Bornology WeakBilin
lemma _root_.WeakBilin.isVonNBounded_iff (s : Set (WeakBilin B)) :
    IsVonNBounded 𝕜 s ↔ ∀ y, IsVonNBounded 𝕜 (((pairing B).flip y) '' s) :=
  WeakBilin.isInducing B |>.isVonNBounded_iff (pairing B).flip s

/-- Weak topologies induced by bilinear forms with equivalent dual spaces are continuously
linearly equivalent. -/
@[simps!]
def _root_.WeakBilin.continuousLinearEquiv (e : F ≃ₗ[𝕜] F') (B' : E →ₗ[𝕜] F' →ₗ[𝕜] 𝕜)
    (hB : (e.arrowCongr (.refl ..) B.flip).flip = B') :
    WeakBilin B ≃L[𝕜] WeakBilin B' where
  toLinearEquiv := linearEquiv 𝕜 B |>.trans <| (linearEquiv 𝕜 B').symm
  continuous_toFun := by
    apply continuous_of_continuous_eval B' fun y' ↦ ?_
    simp only [DFunLike.ext_iff, flip_apply, LinearEquiv.arrowCongr_apply,
      LinearEquiv.refl_apply] at hB
    simp only [← hB]
    exact eval_continuous B _
  continuous_invFun := by
    apply continuous_of_continuous_eval B fun y ↦ ?_
    simp only [DFunLike.ext_iff, flip_apply, LinearEquiv.arrowCongr_apply,
      LinearEquiv.refl_apply] at hB
    rw [← e.symm_apply_apply y]
    simp only [hB]
    exact eval_continuous B' _

end NormedField

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

variable {B} in
open Bornology WeakBilin in
lemma _root_.WeakBilin.isVonNBounded_iff_bddAbove {s : Set (WeakBilin B)} :
    IsVonNBounded 𝕜 s ↔ ∀ y, BddAbove ((‖(pairing B).flip y ·‖) '' s) := by
  have (y : F) : BddBelow ((‖pairing B · y‖) '' s) := ⟨0, by rintro - ⟨_, -, rfl⟩; positivity⟩
  rw [WeakBilin.isVonNBounded_iff]
  congr! with y
  rw [← Bornology.isBounded_iff_isVonNBounded, NormedSpace.vonNBornology_eq 𝕜,
    ← isBounded_norm_iff, Set.image_image, isBounded_iff_bddBelow_bddAbove]
  simp [this]




open scoped Topology
open WeakBilin Bornology
lemma absorbent_polar_iff_isVonNBounded {s : Set (WeakBilin B)} :
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


end NontriviallyNormedField

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
noncomputable def seminorm (s : Set α) :
    Seminorm 𝕜 (α →ᵤ[𝔖] β) where
  toFun f := ⨆ x : s, ‖toFun 𝔖 f x‖
  map_zero' := by simp
  add_le' := sorry
  neg' := by simp
  smul' := by simp [norm_smul, Real.mul_iSup_of_nonneg (norm_nonneg _)]

lemma seminorm_apply (s : Set α) (f : α →ᵤ[𝔖] β) :
    seminorm 𝕜 s f = ⨆ x : s, ‖toFun 𝔖 f x‖ := rfl

variable (𝕜 α β 𝔖) in
/-- lazy -/
noncomputable def seminormFamily : SeminormFamily 𝕜 (α →ᵤ[𝔖] β) 𝔖 :=
  fun s ↦ seminorm 𝕜 s.1

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

lemma seminorm_le_of_subset {s t : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) (hst : s ⊆ t) :
    seminorm B 𝔖 s hs ≤ seminorm B 𝔖 t ht := by
  intro x
  simp only
  rw [seminorm_apply_le_iff hs]
  sorry

lemma seminorm_union {s t : Set (WeakBilin B.flip)} (hs : IsVonNBounded 𝕜 s)
      (ht : IsVonNBounded 𝕜 t) :
    seminorm B 𝔖 (s ∪ t) (hs.union ht) = seminorm B 𝔖 s hs ⊔ seminorm B 𝔖 t ht := by
  ext
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simp
  obtain (rfl | ht_non) := t.eq_empty_or_nonempty; · simp
  exact isLUB_seminorm (hs.union ht) hs_non.inl _ |>.unique <|
    (Set.image_union ..) ▸ (isLUB_seminorm hs hs_non _).union (isLUB_seminorm ht ht_non _)

lemma continuous_seminorm (h𝔖_non : 𝔖.Nonempty) (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖)
      (s : Set (WeakBilin B.flip)) (hs_mem : s ∈ 𝔖) (hs : IsVonNBounded 𝕜 s) :
    Continuous (seminorm B 𝔖 s hs) := by
  have := UniformConvergenceCLM.hasBasis_nhds_zero_of_basis'
    (RingHom.id 𝕜) 𝕜 𝔖 h𝔖_non h𝔖_dir Metric.nhds_basis_ball
    |>.comap (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖))
  apply Seminorm.continuous_of_continuousAt_zero
  rw [← map_zero (toUniformConvergenceCLM (B := B) (𝔖 := 𝔖)), ← nhds_induced] at this
  simp only [Metric.mem_ball, dist_zero_right] at this
  rw [ContinuousAt, this.tendsto_iff Metric.nhds_basis_closedBall]
  intro ε hε
  simp only [preimage_setOf_eq, toUniformConvergenceCLM_apply_apply, mem_setOf_eq,
    map_zero, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    Prod.exists]
  simp only [seminorm_apply, LinearMap.flip_apply]
  refine ⟨s, ε, ⟨hs_mem, hε⟩, fun x hx ↦ ?_⟩
  rw [abs_of_nonneg (Real.sSup_image_nonneg fun _ _ ↦ by positivity)]
  obtain (rfl | h) := s.eq_empty_or_nonempty; · simpa using hε.le
  apply csSup_le (h.image _)
  rintro - ⟨y, hy, rfl⟩
  exact (hx y hy).le

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

open scoped Pointwise in
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
  simp

  sorry

#exit

open scoped ComplexOrder

instance [Module ℝ E] [h : IsScalarTower ℝ 𝕜 E] (h𝔖_non : 𝔖.Nonempty)
    (h𝔖_dir : DirectedOn (· ⊆ ·) 𝔖) (h𝔖 : ∀ s ∈ 𝔖, IsVonNBounded 𝕜 s) :
    LocallyConvexSpace ℝ (PolarTopology B 𝔖) :=
  (withSeminorms B 𝔖 h𝔖_non h𝔖_dir h𝔖 ).toLocallyConvexSpace

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
