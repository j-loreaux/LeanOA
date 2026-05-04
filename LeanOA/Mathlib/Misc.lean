module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

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

-- I think this instance is not terribly crazy.
instance {𝕜 A : Type*} [RCLike 𝕜] [Norm A] [MulAction 𝕜 A] [SMul ℤ A]
    [IsScalarTower ℤ 𝕜 A] [NormSMulClass 𝕜 A] :
    NormSMulClass ℤ A where
  norm_smul z a := by
    rw [← smul_one_smul 𝕜]
    simp only [norm_smul, norm_one, mul_one]

set_option backward.isDefEq.respectTransparency false in
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

lemma DirectedOn.inter {α : Type*} {r : α → α → Prop} {s : Set α}
    [IsTrans α r] (hs : DirectedOn r s) (x₀ : α) :
    DirectedOn r (s ∩ {x | r x₀ x}) := by
  rintro y ⟨hy, y₁⟩ z ⟨hz, h₂⟩
  obtain ⟨w, hw, hyw, hzw⟩ := hs y hy z hz
  exact ⟨w, ⟨hw, trans y₁ hyw⟩ , ⟨hyw, hzw⟩⟩

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

set_option backward.isDefEq.respectTransparency false in
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
