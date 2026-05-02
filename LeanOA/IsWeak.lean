import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
import LeanOA.Mathlib.Topology.Algebra.Module.WeakDual
import LeanOA.Mathlib.Analysis.LocallyConvex.IsCompatible
import LeanOA.Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.LocallyConvex.WeakDual
import LeanOA.Mathlib.Analysis.Normed.Group.Uniform

open Topology Filter

section Basic

variable {α 𝕜 E F E' F' : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]


section

variable [TopologicalSpace E] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- `weakDualPairing` is `topDualPairing` where `StrongDual` is replaced with `WeakDual`. -/
noncomputable def weakDualPairing : WeakDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  StrongDual.toWeakDual.arrowCongr (.refl ..) (topDualPairing 𝕜 E)

variable (𝕜 E) in
/-- `weakSpacePairing 𝕜 E` is `(topDualPairing 𝕜 E).flip` where `E` is replaced with
`WeakSpace 𝕜 E`. -/
noncomputable def weakSpacePairing : WeakSpace 𝕜 E →ₗ[𝕜] (StrongDual 𝕜 E) →ₗ[𝕜] 𝕜 :=
  (toWeakSpace 𝕜 E).arrowCongr (.refl ..) (topDualPairing 𝕜 E).flip

end

/-- Typeclass expressing that the topology on `E` is the weak topology induced
by the bilinear form `B`. -/
@[mk_iff]
class LinearMap.IsWeak [t : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  eq_induced : t = .induced (B · ·) Pi.topologicalSpace

variable [inst : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]

namespace LinearMap.IsWeak

instance : B.flip.flip.IsWeak := hB

/-- The coercion `(fun x y ↦ B x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous : Continuous (B · ·) :=
  hB.eq_induced ▸ continuous_induced_dom

@[fun_prop]
lemma continuous_eval (y : F) : Continuous (B · y) :=
  continuous_pi_iff.mp (coeFn_continuous B) _

lemma continuous_of_continuous_eval {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : ∀ y, Continuous (fun x ↦ B (f x) y)) :
    Continuous f :=
  hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
theorem isInducing : IsInducing (B · ·) where
  eq_induced := hB.eq_induced

variable {B} in
/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
theorem isEmbedding (hB_inj : Function.Injective B) :
    IsEmbedding (B · ·) := by
  convert (LinearMap.coe_injective.comp hB_inj |>.isEmbedding_induced)
  exact hB.eq_induced

variable {B} in
theorem tendsto_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {f : α → E} {x : E}
    (hB_inj : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i ↦ B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB_inj).tendsto_nhds_iff, Function.comp_def]

protected theorem congr [AddCommMonoid E'] [Module 𝕜 E']
    [AddCommMonoid F'] [Module 𝕜 F'] [TopologicalSpace E']
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜) (e : E ≃L[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (hBB' : e.toLinearEquiv.arrowCongr (f.arrowCongr (.refl ..)) B = B') [hB : B.IsWeak] :
    B'.IsWeak where
  eq_induced := by
    have := congr(TopologicalSpace.induced e.symm $(hB.eq_induced))
    rw [e.symm.toHomeomorph.induced_eq.symm]
    apply this.trans
    rw [induced_compose]
    simp_rw [← hBB', induced_to_pi]
    rw [f.toEquiv.iInf_congr]
    intro y
    congr!
    simp

/--
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
def eval [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] : F →ₗ[𝕜] StrongDual 𝕜 E where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

include hB in
/-- Addition in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak` topology. -/
theorem continuousAdd [ContinuousAdd 𝕜] : ContinuousAdd E := by
  rw [hB.eq_induced]
  let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
  have : B.IsWeak := ⟨rfl⟩
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_add, add_apply]
  fun_prop

include hB in
/-- Scalar multiplication in `E` is continuous when `E` is equipped with a `LinearMap.IsWeak`
topology. -/
theorem continuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 E := by
  rw [hB.eq_induced]
  let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
  have : B.IsWeak := ⟨rfl⟩
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_smul, smul_apply]
  fun_prop

/-- `E` is a `IsTopologicalAddGroup` when `E` is equipped with a `LinearMap.IsWeak` topology. -/
theorem isTopologicalAddGroup {𝕜 E F : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    [ContinuousAdd 𝕜] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] : IsTopologicalAddGroup E where
  toContinuousAdd := continuousAdd B
  continuous_neg := by
    rw [hB.eq_induced]
    let t₁ : TopologicalSpace E := .induced (B · ·) Pi.topologicalSpace
    have : B.IsWeak := ⟨rfl⟩
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    simp_rw [Function.comp_apply, map_neg, neg_apply, ← map_neg (B _)]
    fun_prop

lemma separatingLeft_of_t1Space [T1Space 𝕜] [T1Space E] : B.SeparatingLeft := by
  intro x h
  rw [← specializes_iff_eq, ← (isInducing B).specializes_iff, specializes_iff_eq]
  simpa [funext_iff]

variable [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]

open WeakBilin in
instance (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : (pairing B).IsWeak where
  eq_induced := rfl

instance : (weakDualPairing 𝕜 E).IsWeak where
  eq_induced := rfl

instance : (weakSpacePairing 𝕜 E).IsWeak where
  eq_induced := rfl

open WeakBilin in
instance (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : (pairing (pairing B.flip).flip).IsWeak :=
  LinearMap.IsWeak.congr (pairing B) _ (.refl ..) (WeakBilin.linearEquiv 𝕜 B.flip).symm rfl

instance {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsCompatible] :
    letI B' : WeakSpace 𝕜 E →ₗ[𝕜] F →ₗ[𝕜] 𝕜 := (toWeakSpace 𝕜 E).arrowCongr (.refl ..) B
    B'.IsWeak :=
  LinearMap.IsWeak.congr (weakSpacePairing 𝕜 E) _ (.refl ..) hB.equiv.symm rfl

/-- Continuous linear equivalence of `F` with `WeakDual 𝕜 E` from `B.IsCompatible` and
`B.flip.IsWeak` . -/
noncomputable
def _root_.LinearMap.IsCompatible.weakDualCLE' {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB' : B.IsCompatible] [hB : B.flip.IsWeak] :
    F ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := hB'.equiv ≪≫ₗ StrongDual.toWeakDual
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval fun f ↦ ?_
    simpa [hB'.equiv_apply_apply] using hB.continuous_eval B.flip f
  continuous_invFun := by
    apply hB.continuous_of_continuous_eval _ fun x ↦ ?_
    simpa [← hB'.equiv_apply_apply] using WeakDual.eval_continuous x

end LinearMap.IsWeak

end Basic

namespace LinearMap.IsWeak
section Topology

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace E]

theorem withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 E) :=
  let e : F ≃ (Σ _ : F, Fin 1) := .symm <| .sigmaUnique _ _
  hB.eq_induced ▸ withSeminorms_induced (withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜))
    (LinearMap.ltoFun 𝕜 F 𝕜 𝕜 ∘ₗ B : E →ₗ[𝕜] (F → 𝕜)) |>.congr_equiv e

theorem hasBasis_nhds_zero (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] :
    (𝓝 (0 : E)).HasBasis (· ∈ B.toSeminormFamily.basisSets) _root_.id :=
  withSeminorms B |>.hasBasis

open Bornology

lemma isVonNBounded_iff (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] (s : Set E) :
    IsVonNBounded 𝕜 s ↔ ∀ y, IsVonNBounded 𝕜 (B.flip y '' s) :=
  hB.isInducing B |>.isVonNBounded_iff B.flip s

variable {B} in
lemma isVonNBounded_iff_bddAbove {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] {s : Set E} :
    IsVonNBounded 𝕜 s ↔ ∀ y, BddAbove ((‖B.flip y ·‖) '' s) := by
  have (y : F) : BddBelow ((‖B · y‖) '' s) := ⟨0, by rintro - ⟨_, -, rfl⟩; positivity⟩
  rw [isVonNBounded_iff B]
  congr! with y
  rw [← Bornology.isBounded_iff_isVonNBounded, NormedSpace.vonNBornology_eq 𝕜,
    ← isBounded_norm_iff, Set.image_image, isBounded_iff_bddBelow_bddAbove]
  simp [this]

end Topology

section LocallyConvex

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]

section

variable [TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]

/-- The **Weak Representation Theorem**: Every continuous functional on `E` endowed with
the `σ(E, F; B)`-topology is of the form `x ↦ B(x, y)` for some `y : F`. -/
theorem eval_surjective : Function.Surjective (eval B) := fun f ↦ by
  have : f.toLinearMap ∈
      Submodule.span 𝕜 (ContinuousLinearMap.coeLM 𝕜 ∘ₗ eval B).range := by
    simpa [coe_range, mem_span_iff_continuous, continuous_iff_le_induced, ← induced_to_pi]
      using hB.eq_induced ▸ f.continuous.le_induced
  simpa

lemma eval_injective (hr : B.SeparatingRight) : Function.Injective (eval B) := by
  simpa [injective_iff_map_eq_zero, DFunLike.ext_iff]

/-- When `B` is right-separating, `F` is linearly equivalent to the strong dual of `E` with the
weak topology. -/
noncomputable def rightDualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] StrongDual 𝕜 E :=
  .ofBijective (eval B) ⟨eval_injective B hr, eval_surjective B⟩

end

/-- When `B` is left-separating, `E` is linearly equivalent to the strong dual of `F` with the
weak topology. -/
noncomputable def leftDualEquiv [TopologicalSpace F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    [hB : B.flip.IsWeak] (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] StrongDual 𝕜 F :=
  rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

variable [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

theorem locallyConvexSpace (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak] :
    LocallyConvexSpace ℝ E :=
  withSeminorms B |>.toLocallyConvexSpace

end LocallyConvex

end LinearMap.IsWeak
