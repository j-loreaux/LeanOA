import Mathlib.Analysis.CStarAlgebra.Spectrum

theorem spectrum.norm_eq_one_of_unitary {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E]
    [StarRing E] [CStarRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] {u : E} (hu : u ∈ unitary E)
    ⦃z : 𝕜⦄ (hz : z ∈ spectrum 𝕜 u) : ‖z‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary hu hz
