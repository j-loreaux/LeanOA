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

open scoped ComplexStarModule

open Complex in
/-- An element in a non-unital star `ℂ`-algebra is normal if and only if its real and imaginary
parts commute. -/
lemma isStarNormal_iff_commute_realPart_imaginaryPart
    {A : Type*} [NonUnitalNonAssocRing A] [StarRing A]
    [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    {x : A} : IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A) := by
  conv_lhs => rw [isStarNormal_iff, ← realPart_add_I_smul_imaginaryPart x]
  rw [commute_iff_eq]
  simp only [star_add, selfAdjoint.star_val_eq, star_smul, RCLike.star_def, Complex.conj_I,
    neg_smul, ← sub_eq_add_neg, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub,
    smul_smul, Complex.I_mul_I, one_smul, sub_neg_eq_add, mul_sub, add_mul, smul_add]
  rw [sub_eq_add_neg, add_assoc, add_sub_assoc, add_left_cancel_iff, ← sub_add,
    ← add_assoc, add_right_cancel_iff, ← sub_eq_zero]
  noncomm_ring
  rw [add_comm, neg_smul, ← sub_eq_add_neg, sub_eq_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ congr(2 • I • $h)⟩
  have := congr(I • (2⁻¹ : ℂ) • $h)
  rw [← smul_one_smul ℂ (2 : ℤ) (I • (ℑ x * ℜ x : A)), ← smul_one_smul ℂ (2 : ℤ)] at this
  simpa

lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq {A : Type*} [NonUnitalNonAssocRing A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    {x : A} [hx : IsStarNormal x] : star x * x = ℜ x * ℜ x + ℑ x * ℑ x := by
   -- seriously? we have to do this?
  have : IsAddTorsionFree A :=  have : Module ℚ A := RestrictScalars.module ℚ ℝ A; .of_module_rat A
  apply nsmul_right_injective two_ne_zero
  simp only
  nth_rw 1 [two_nsmul, star_comm_self' x, add_comm, star_mul_self_add_self_mul_star]

theorem ext_iff_realPart_and_imaginaryPart {A : Type*} [NonUnitalNonAssocRing A] [StarRing A]
    [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A] {x y : A} :
    x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x, h.1, h.2]
  simp [realPart_add_I_smul_imaginaryPart]

lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one {A : Type*} [Ring A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A] {x : A} :
    x ∈ unitary A ↔ IsStarNormal x ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A) := by
  rw [Unitary.mem_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hx, h⟩ ↦ ?_⟩
  · have : IsStarNormal x := by simp [isStarNormal_iff, commute_iff_eq, h]
    refine ⟨this, ?_⟩
    rw [star_mul_self_eq_realPart_sq_add_imaginaryPart_sq] at h
    simp [sq, h]
  · simp only [← hx.star_comm_self.eq, and_self]
    simp [star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq, h]

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
