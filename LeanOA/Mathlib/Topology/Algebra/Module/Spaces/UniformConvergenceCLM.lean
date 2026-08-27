module

public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM

@[expose] public section

section

/- This just needs a small PR to remove the defeq abuse. -/

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

end
