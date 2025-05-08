import Mathlib.Analysis.CStarAlgebra.Basic

variable {𝕜 A : Type*} [NormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A]
    [NormedField 𝕜] [NormedSpace 𝕜 A] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 A]

noncomputable instance : NormedSpace 𝕜 (selfAdjoint A) where
  norm_smul_le := by simp [norm_smul]
