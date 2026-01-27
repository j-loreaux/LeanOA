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

open Uniformity in
theorem Metric.uniformity_basis_dist_le_inv_nat_succ {α : Type*} [PseudoMetricSpace α] :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩

open Topology in
theorem Metric.nhds_basis_closedBall_inv_nat_succ {α : Type*} [PseudoMetricSpace α] {x : α} :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ

@[simp]
theorem ker_imaginaryPart {E : Type*} [AddCommGroup E]
    [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E] :
    imaginaryPart.ker = selfAdjoint.submodule ℝ E := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

open ComplexStarModule in
@[simp]
lemma imaginaryPart_eq_zero_iff {A : Type*} [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] {x : A} :
    ℑ x = 0 ↔ IsSelfAdjoint x := by
  simpa [-ker_imaginaryPart] using SetLike.ext_iff.mp ker_imaginaryPart x

-- I think this instance is not terribly crazy.
instance {𝕜 A : Type*} [RCLike 𝕜] [Norm A] [MulAction 𝕜 A] [SMul ℤ A]
    [IsScalarTower ℤ 𝕜 A] [NormSMulClass 𝕜 A] :
    NormSMulClass ℤ A where
  norm_smul z a := by
    rw [← smul_one_smul 𝕜]
    simp only [norm_smul, norm_one, mul_one]
