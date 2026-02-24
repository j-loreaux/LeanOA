import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- `Analysis.Normed.Module.Basic`
@[simp]
lemma norm_smul_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    ‖x‖ • ‖x‖⁻¹ • x = x :=
  NormedSpace.norm_smul_normalize x

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

-- I think this instance is not terribly crazy.
instance {𝕜 A : Type*} [RCLike 𝕜] [Norm A] [MulAction 𝕜 A] [SMul ℤ A]
    [IsScalarTower ℤ 𝕜 A] [NormSMulClass 𝕜 A] :
    NormSMulClass ℤ A where
  norm_smul z a := by
    rw [← smul_one_smul 𝕜]
    simp only [norm_smul, norm_one, mul_one]

open NNReal in
/-- The collection of nonnegative elements as an `ℝ≥0`-submodule. -/
def Nonneg.nnrealSubmodule (α : Type*) [AddCommGroup α] [PartialOrder α] [Module ℝ α]
    [IsOrderedAddMonoid α] [IsStrictOrderedModule ℝ α] :
    Submodule ℝ≥0 α where
  carrier := {x | 0 ≤ x}
  zero_mem' := le_rfl
  add_mem' := add_nonneg
  smul_mem' r _ h := smul_nonneg r.2 h

open ComplexOrder in
@[simp]
theorem Complex.real_le_zero {x : ℝ} : (x : ℂ) ≤ 0 ↔ x ≤ 0 := by
  simp [← ofReal_zero]

open ComplexOrder in
@[simp]
theorem Complex.real_lt_zero {x : ℝ} : (x : ℂ) < 0 ↔ x < 0 := by
  simp [← ofReal_zero]

@[to_dual directedOn_iff_isCodirectedOrder]
lemma directedOn_iff_isDirectedOrder {α : Type*} [LE α] {s : Set α} :
    DirectedOn (· ≤ ·) s ↔ IsDirectedOrder s := by
  rw [directedOn_iff_directed]
  exact ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

lemma DirectedOn.inter {α : Type*} {r : α → α → Prop} {s : Set α}
    [IsTrans α r] (hs : DirectedOn r s) (x₀ : α) :
    DirectedOn r (s ∩ {x | r x₀ x}) := by
  rintro y ⟨hy, y₁⟩ z ⟨hz, h₂⟩
  obtain ⟨w, hw, hyw, hzw⟩ := hs y hy z hz
  exact ⟨w, ⟨hw, trans y₁ hyw⟩ , ⟨hyw, hzw⟩⟩

open Filter in
-- `Cauchy.map` should be protected.
lemma _root_.Cauchy.map_of_le {α β : Type*} [UniformSpace α] [UniformSpace β]
    {l : Filter α} {f : α → β} (hl : Cauchy l) {s : Set α}
    (hf : UniformContinuousOn f s) (hls : l ≤ 𝓟 s) :
    Cauchy (map f l) := by
  rw [uniformContinuousOn_iff_restrict] at hf
  have hl' : Cauchy (comap (Subtype.val : s → α) l) := by
    apply hl.comap' ?_ (comap_coe_neBot_of_le_principal (h := hl.1) hls)
    exact le_def.mpr fun x a ↦ a
  simpa [Set.restrict_def, ← Function.comp_def, ← map_map,
    subtype_coe_map_comap, inf_eq_left.mpr hls] using hl'.map hf

section UniformEquiv

namespace Continuous

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]
  [CompactSpace X] [T2Space Y] (f : X ≃ Y) (hf : Continuous f)

/-- A continuous bijection from a compact space to a Hausdorff space is in fact a uniform
equivalence whenever the domain and codomain are equipped with a uniform structure. -/
def uniformOfEquivCompactToT2 : X ≃ᵤ Y where
  toEquiv := f
  uniformContinuous_toFun := CompactSpace.uniformContinuous_of_continuous hf
  uniformContinuous_invFun :=
    let h : X ≃ₜ Y := hf.homeoOfEquivCompactToT2
    let _ : CompactSpace Y := h.compactSpace
    CompactSpace.uniformContinuous_of_continuous (map_continuous h.symm)

@[simp]
lemma uniformOfEquivCompactToT2_apply (x : X) :
    hf.uniformOfEquivCompactToT2 f x = f x :=
  rfl

@[simp]
lemma uniformOfEquivCompactToT2_symm_apply (y : Y) :
    hf.uniformOfEquivCompactToT2.symm y = f.symm y :=
  rfl

@[simp]
lemma toHomeomorph_uniformOfEquivCompactToT2 :
    hf.uniformOfEquivCompactToT2.toHomeomorph = hf.homeoOfEquivCompactToT2 :=
  rfl

@[simp]
lemma toEquiv_uniformOfEquivCompactToT2 :
    hf.uniformOfEquivCompactToT2.toEquiv = f :=
  rfl

end Continuous

section normedSpaceClosedUnitBall
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ComplexOrder Set Metric

theorem subsingleton_of_zero_mem_extremePoints_closedUnitBall
    (h : 0 ∈ extremePoints 𝕜 (closedBall (0 : H) 1)) : Subsingleton H := by
  by_contra!
  obtain ⟨y, hy⟩ := exists_ne (0 : H)
  set z := (1 / ‖y‖ : 𝕜) • y
  have hz : z ∈ closedBall (0 : H) 1 ∧ ‖z‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hy, z]
  simp only [mem_extremePoints, mem_closedBall, dist_zero_right] at h
  have := h.2 z hz.2.le (-z) (norm_neg z ▸ hz.2.le) ⟨1 / 2, ⟨1 / 2, by simp [-one_div]⟩⟩
  simp_all

theorem norm_eq_one_of_mem_extremePoints_closedUnitBall [Nontrivial H] {x : H}
    (hx : x ∈ extremePoints 𝕜 (closedBall (0 : H) 1)) : ‖x‖ = 1 := by
  have h : x ≠ 0 := fun h ↦
    have := subsingleton_of_zero_mem_extremePoints_closedUnitBall (h ▸ hx)
    false_of_nontrivial_of_subsingleton H
  simp only [mem_extremePoints, mem_closedBall, dist_zero_right] at hx
  by_contra!
  refine h (@hx.2 ((1 / ‖x‖ : 𝕜) • x) ?_ 0 (by simp) ⟨‖x‖, 1 - ‖x‖, by simp_all, ?_, ?_⟩).2.symm
  on_goal 2 => rw [sub_pos, ← RCLike.ofReal_one (K := 𝕜), RCLike.ofReal_lt_ofReal]; grind
  all_goals simp [norm_smul, norm_ne_zero_iff.mpr h]

end normedSpaceClosedUnitBall

end UniformEquiv

/-! ## Unnecessary

These lemmas are not currently necessary for anything in LeanOA.
-/

lemma IsClosed.setOf_isSelfAdjoint {R : Type*} [Star R]
    [TopologicalSpace R] [ContinuousStar R] [T2Space R] :
    IsClosed {x : R | IsSelfAdjoint x} :=
  isClosed_eq continuous_star continuous_id

/-- A linear map with closed kernel of finite index is continuous. -/
lemma LinearMap.continuous_of_isClosed_ker_of_finiteDimensional
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
    [CompleteSpace 𝕜]
    (f : E →ₗ[𝕜] F) (hf : IsClosed (f.ker : Set E))
    (hf_findim : FiniteDimensional 𝕜 (E ⧸ f.ker)) :
    Continuous f :=
  have h : Continuous (Quotient.mk _ : E → E ⧸ f.ker) := { isOpen_preimage := fun _ a ↦ a }
  f.ker.liftQ f le_rfl |>.continuous_of_finiteDimensional.comp h

instance ContinuousSMul.smulMemClass (S M α : Type*) [Monoid M] [MulAction M α]
    [TopologicalSpace M] [TopologicalSpace α] [ContinuousSMul M α] [SetLike S α]
    [SMulMemClass S M α] (s : S) : ContinuousSMul M s where
  continuous_smul := by fun_prop

instance ContinuousSMul.complexToReal {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : ContinuousSMul ℝ E :=
  IsScalarTower.continuousSMul ℂ

instance selfAdjoint.instContinuousSMul {R A : Type*} [Star R] [TrivialStar R]
    [AddGroup A] [StarAddMonoid A] [SMul R A] [StarModule R A] [TopologicalSpace R]
    [TopologicalSpace A] [ContinuousSMul R A] : ContinuousSMul R (selfAdjoint A) where
  continuous_smul := by
    rw [continuous_induced_rng]
    fun_prop

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
