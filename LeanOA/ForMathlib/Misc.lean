import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace

-- `Analysis.Normed.Module.Basic`
@[simp]
lemma norm_smul_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    ‖x‖ • ‖x‖⁻¹ • x = x :=
  NormedSpace.norm_smul_normalize x

open Complex in
lemma spectrum_subset_slitPlane_of_norm_lt_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    {u : A} (hu : ‖u - 1‖ < 1) :
    spectrum ℂ u ⊆ slitPlane := by
  have := spectrum.subset_closedBall_norm (𝕜 := ℂ) (u - 1) |>.trans <|
    Metric.closedBall_subset_ball hu
  rw [← map_one (algebraMap ℂ A), ← spectrum.sub_singleton_eq, Set.sub_singleton] at this
  exact fun x hx ↦ add_sub_cancel 1 x ▸
    Complex.mem_slitPlane_of_norm_lt_one (by simpa using this ⟨x, hx, rfl⟩)

lemma ContinuousLinearMap.norm_postcomp_le {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NontriviallyNormedField 𝕜₁]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃}
    {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] [RingHomIsometric σ] [RingHomIsometric τ]
    [RingHomIsometric ρ] {E F G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜₁ E] [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F] [SeminormedAddCommGroup G]
    [NormedSpace 𝕜₃ G] (L : F →SL[τ] G) :
    ‖L.postcomp (σ := σ) E‖ ≤ ‖L‖ :=
  L.postcomp (σ := σ) E |>.opNorm_le_bound (by positivity) <| opNorm_comp_le L

@[to_additive]
theorem Subgroup.topologicalClosure_mono {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {s t : Subgroup G} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h
