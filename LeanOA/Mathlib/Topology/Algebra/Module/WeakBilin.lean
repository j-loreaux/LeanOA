import Mathlib.Topology.Algebra.Module.WeakBilin

variable {𝕜 E F : Type*}

namespace WeakBilin

/-- The canonical linear equivalence (over `𝕝`) between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`
and `E`. -/
def linearEquiv (𝕝 : Type*) [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [CommSemiring 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WeakBilin B ≃ₗ[𝕝] E :=
  LinearEquiv.refl ..

/-- The dual pairing between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `F`. In order to avoid abuse
of the definitional equality between `E` and `WeakBilin B`, it is necessary to use this pairing
instead of `B` itself when considering statements involving the weak topology induced by the
pairing, such as the bipolar theorem. -/
def pairing [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WeakBilin B →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  (linearEquiv 𝕜 B).symm.arrowCongr (.refl _ _) B

end WeakBilin
