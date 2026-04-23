import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
import LeanOA.Mathlib.Topology.Algebra.Module.WeakDual
import LeanOA.Mathlib.Analysis.LocallyConvex.IsCompatible

open Topology Filter

variable {α 𝕜 E F E' F' : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F]


section

variable [TopologicalSpace E] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- `weakDualPairing` is `topDualPairing` where `StrongDual` is replaced with `WeakDual`. -/
def weakDualPairing : WeakDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  StrongDual.toWeakDual.arrowCongr (.refl ..) (topDualPairing 𝕜 E)

variable (𝕜 E) in
/-- `weakSpacePairing 𝕜 E` is `(topDualPairing 𝕜 E).flip` where `E` is replaced with
`WeakSpace 𝕜 E`. -/
def weakSpacePairing : WeakSpace 𝕜 E →ₗ[𝕜] (StrongDual 𝕜 E) →ₗ[𝕜] 𝕜 :=
  (toWeakSpace 𝕜 E).arrowCongr (.refl ..) (topDualPairing 𝕜 E).flip

end

@[mk_iff]
class LinearMap.IsWeak [t : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  eq_induced : t = .induced (B · ·) Pi.topologicalSpace

variable [inst : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]

namespace LinearMap.IsWeak

@[fun_prop]
lemma continuous_eval (y : F) : Continuous (B · y) :=
  continuous_pi_iff.mp (hB.eq_induced ▸ continuous_induced_dom) _

lemma continuous_of_continuous_eval {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : ∀ y, Continuous (fun x ↦ B (f x) y)) :
    Continuous f :=
  hB.eq_induced ▸ continuous_induced_rng.mpr (continuous_pi_iff.mpr hf)

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

protected theorem LinearMap.IsWeak.congr [AddCommMonoid E'] [Module 𝕜 E']
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

variable [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]

/--
Map `F` into the topological dual of `E` with the weak topology induced by `F`
-/
def eval : F →ₗ[𝕜] StrongDual 𝕜 E where
  toFun f := ⟨B.flip f, by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

open WeakBilin in
instance : (pairing B).IsWeak where
  eq_induced := rfl

instance : (weakDualPairing 𝕜 E).IsWeak where
  eq_induced := rfl

instance : (weakSpacePairing 𝕜 E).IsWeak where
  eq_induced := rfl

open WeakBilin in
instance : (pairing (pairing B.flip).flip).IsWeak :=
  LinearMap.IsWeak.congr (pairing B) _ (.refl ..) (WeakBilin.linearEquiv 𝕜 B.flip).symm rfl

instance {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsCompatible] :
    letI B' : WeakSpace 𝕜 E →ₗ[𝕜] F →ₗ[𝕜] 𝕜 := (toWeakSpace 𝕜 E).arrowCongr (.refl ..) B
    B'.IsWeak :=
  LinearMap.IsWeak.congr (weakSpacePairing 𝕜 E) _ (.refl ..) hB.equiv.symm rfl

end LinearMap.IsWeak
