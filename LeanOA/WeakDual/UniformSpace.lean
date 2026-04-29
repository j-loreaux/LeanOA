import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi

namespace WeakBilin

variable {𝕜 E F : Type*}
variable [UniformSpace 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The uniform structure on `WeakBilin B` induced by the uniform structure on `𝕜`. -/
instance instUniformSpace : UniformSpace (WeakBilin B) :=
  UniformSpace.comap (B · ·) (Pi.uniformSpace fun _ ↦ 𝕜)

-- verify that the uniform structure induces the pre-existing topological structure.
example : (instUniformSpace B).toTopologicalSpace = instTopologicalSpace B := by
  with_reducible_and_instances rfl

lemma cauchy_iff {l : Filter (WeakBilin B)} : Cauchy l ↔ ∀ y, Cauchy (Filter.map (B · y) l) :=
  cauchy_comap_uniformSpace (u := Pi.uniformSpace fun _ : F ↦ 𝕜) (f := (B · ·)) |>.trans
    <| cauchy_pi_iff _

end WeakBilin

namespace WeakDual

variable {𝕜 E : Type*} [CommSemiring 𝕜] [UniformSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

variable (𝕜 E) in
/-- The uniform structure on `WeakBilin B` induced by the uniform structure on `𝕜`. -/
instance instUniformSpace : UniformSpace (WeakDual 𝕜 E) :=
  WeakBilin.instUniformSpace (topDualPairing 𝕜 E)

-- verify that the uniform structure induces the pre-existing topological structure.
example : (instUniformSpace 𝕜 E).toTopologicalSpace = instTopologicalSpaceWeakDual 𝕜 E := by
  with_reducible_and_instances rfl

lemma cauchy_iff {l : Filter (WeakDual 𝕜 E)} :
    Cauchy l ↔ ∀ x : E, Cauchy (Filter.map (topDualPairing 𝕜 E · x) l) :=
  WeakBilin.cauchy_iff (topDualPairing 𝕜 E)

end WeakDual
