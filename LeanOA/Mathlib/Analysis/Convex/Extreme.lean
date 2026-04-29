import Mathlib.Analysis.Convex.Extreme

@[nontriviality]
lemma Set.extremePoints_eq_self {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [Subsingleton E] (A : Set E) :
    Set.extremePoints 𝕜 A = A :=
  subset_antisymm extremePoints_subset fun _ h ↦ ⟨h, fun _ _ _ _ _ ↦ Subsingleton.elim ..⟩
