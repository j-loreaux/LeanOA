import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Topology.Algebra.Module.Equiv

variable {𝕜 E F E' F' : Type*}
  [CommSemiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  [AddCommMonoid E'] [Module 𝕜 E'] [AddCommMonoid F'] [Module 𝕜 F']
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
namespace WeakBilin

/-- The canonical linear equivalence (over `𝕝`) between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`
and `E`. -/
def linearEquiv (𝕝 : Type*) [CommSemiring 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WeakBilin B ≃ₗ[𝕝] E :=
  LinearEquiv.refl ..

/-- The dual pairing between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `F`. In order to avoid abuse
of the definitional equality between `E` and `WeakBilin B`, it is necessary to use this pairing
instead of `B` itself when considering statements involving the weak topology induced by the
pairing, such as the bipolar theorem. -/
def pairing : WeakBilin B →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  (linearEquiv 𝕜 B).symm.arrowCongr (.refl _ _) B

variable {B} in
lemma pairing_apply (x : WeakBilin B) :
    pairing B x = B (linearEquiv 𝕜 B x) :=
  rfl

variable [TopologicalSpace 𝕜]

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous' : Continuous fun (x : WeakBilin B) y => pairing B x y :=
  continuous_induced_dom

@[fun_prop]
theorem eval_continuous' (y : F) : Continuous fun x : WeakBilin B => pairing B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y

theorem continuous_of_continuous_eval' {α : Type*} [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => pairing B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

lemma isInducing (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Topology.IsInducing (fun x i ↦ pairing B x i) where
  eq_induced := rfl

/-- Weak topologies induced by equivalent bilinear forms are continuously linearly equivalent. -/
@[simps!]
protected def congr (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (e : E ≃ₗ[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜) (hB : e.arrowCongr (f.arrowCongr (.refl ..)) B = B') :
    WeakBilin B ≃L[𝕜] WeakBilin B' where
  toLinearEquiv := linearEquiv 𝕜 B ≪≫ₗ e ≪≫ₗ (linearEquiv 𝕜 B').symm
  continuous_toFun := by
    apply continuous_of_continuous_eval' B' fun y' ↦ ?_
    simp_rw [pairing_apply]
    simpa [← hB] using WeakBilin.eval_continuous' B _
  continuous_invFun := by
    apply continuous_of_continuous_eval' B fun y ↦ ?_
    simp_rw [pairing_apply]
    simp only [DFunLike.ext_iff, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply] at hB
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [← f.symm_apply_apply y]
    simp only [hB]
    exact eval_continuous B' _

end WeakBilin
