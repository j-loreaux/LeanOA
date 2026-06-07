module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

public section

/-- A class which encodes a specified isometric linear isomorpism between `M`
and the strong dual of `P`, so that we may treat `P` as a predual of `M`. -/
class Predual (𝕜 M P : Type*) [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] where
  /-- A linear isometric equivalence between `M` and the dual of its predual `P`. -/
  equivDual : M ≃ₗᵢ[𝕜] StrongDual 𝕜 P
