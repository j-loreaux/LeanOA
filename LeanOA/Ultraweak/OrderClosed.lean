import LeanOA.Ultraweak.Basic
import LeanOA.KreinSmulian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

open scoped NNReal

variable {M P : Type*}
  [CStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

open scoped Ultraweak

lemma isSelfAdjoint_ofUltraweak {x : σ(M, P)} :
    IsSelfAdjoint (ofUltraweak x) ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff, ← Ultraweak.ofUltraweak_star]

alias ⟨IsSelfAdjoint.of_ofUltraweak, IsSelfAdjoint.ofUltraweak⟩ := isSelfAdjoint_ofUltraweak

lemma isSelfAdjoint_toUltraweak {x : M} :
    IsSelfAdjoint (toUltraweak ℂ P x) ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff, ← Ultraweak.toUltraweak_star]

alias ⟨IsSelfAdjoint.of_toUltraweak, IsSelfAdjoint.toUltraweak⟩ := isSelfAdjoint_toUltraweak

namespace Ultraweak

-- Should go in `Basic`
scoped instance : StarModule ℂ σ(M, P) := inferInstanceAs (StarModule ℂ M)
instance : T2Space σ(M, P) := (weakDualCLE ℂ M P).symm.toHomeomorph.t2Space
instance [Nontrivial M] : Nontrivial σ(M, P) := linearEquiv ℂ M P |>.nontrivial
instance [Subsingleton M] : Subsingleton σ(M, P) := linearEquiv ℂ M P |>.subsingleton



open WeakDual


lemma ofUltraweak_preimage (s : Set M) :
    ofUltraweak ⁻¹' s =
      weakDualCLE ℂ M P ⁻¹' (WeakDual.toStrongDual ⁻¹' (Predual.equivDual.symm ⁻¹' s)) := by
  ext; simp [weakDualCLE]

lemma ofUltraweak_preimage_ball (x : M) (r : ℝ) :
    ofUltraweak ⁻¹' (Metric.ball x r) =
      weakDualCLE ℂ M P ⁻¹' (WeakDual.toStrongDual ⁻¹' (Metric.ball (Predual.equivDual x) r)) := by
  convert ofUltraweak_preimage _
  simp

lemma ofUltraweak_preimage_closedBall (x : M) (r : ℝ) :
    ofUltraweak ⁻¹' (Metric.closedBall x r) =
      weakDualCLE ℂ M P ⁻¹'
        (WeakDual.toStrongDual ⁻¹'
          (Metric.closedBall (Predual.equivDual x) r)) := by
  convert ofUltraweak_preimage _
  simp

variable (P) in
lemma isCompact_closedBall (x : M) (r : ℝ) :
    IsCompact (ofUltraweak ⁻¹' (Metric.closedBall x r) : Set σ(M, P)) := by
  rw [ofUltraweak_preimage_closedBall]
  exact (weakDualCLE ℂ M P).toHomeomorph.isCompact_preimage.mpr <|
    WeakDual.isCompact_closedBall ..

variable (P) in
lemma isClosed_closedBall (x : M) (r : ℝ) :
    IsClosed (ofUltraweak ⁻¹' (Metric.closedBall x r) : Set σ(M, P)) :=
  isCompact_closedBall P x r |>.isClosed

variable [CompleteSpace P]

/-- ugh... so much work just to transfer Krein-Smulian over to `Ultraweak`. -/
protected lemma krein_smulian_of_submodule (S : Submodule ℝ≥0 σ(M, P))
    (hS : IsClosed ((S : Set σ(M, P)) ∩ ofUltraweak ⁻¹' (Metric.closedBall (0 : M) 1))) :
    IsClosed (S : Set σ(M, P)) := by
  have := (weakDualCLE ℂ M P).preimage_symm_preimage (S : Set σ(M, P))
  rw [← this] at hS ⊢
  rw [ofUltraweak_preimage_closedBall, ← Set.preimage_inter] at hS
  apply (weakDualCLE ℂ M P).toHomeomorph.isClosed_preimage.mp at hS
  refine .preimage (map_continuous _) ?_
  simp only [map_zero] at hS
  exact krein_smulian_of_submodule
    (S.comap ((weakDualCLE ℂ M P).symm.restrictScalars ℝ≥0 |>.toLinearMap)) hS

open scoped ComplexStarModule Topology

open Filter Topology in
lemma tendsto_sqrt_one_add_sq_sub_self_atTop :
    Tendsto (fun x : ℝ ↦ √(1 + x ^ 2) - x) atTop (𝓝 0) := by
  -- This can be solved instantaneously with `compute_asymptotics`,
  -- but it isn't yet merged into Mathlib, so it's unavailable here.
  sorry

open Complex in
/-- An element in a non-unital star `ℂ`-algebra is normal if and only if its real and imaginary
parts commute. -/
lemma _root_.isStarNormal_iff_commute_realPart_imaginaryPart
    {A : Type*} [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A]
    {x : A} : IsStarNormal x ↔ Commute (realPart x : A) (imaginaryPart x : A) := by
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

open Complex in
lemma _root_.IsSelfAdjoint.norm_add_I_smul_sq_of_commute {A : Type*}
    [NonUnitalCStarAlgebra A] {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hxy : Commute x y) :
    ‖x + I • y‖ ^ 2 = ‖x * x + y * y‖ := by
  simp [sq, ← CStarRing.norm_star_mul_self, hx.star_eq, hy.star_eq,
    ← sub_eq_add_neg, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm,
    hxy.eq, smul_sub, smul_smul, ← add_assoc]

open Complex in
lemma _root_.IsSelfAdjoint.norm_add_I_smul_le_of_commute {A : Type*}
    [NonUnitalCStarAlgebra A] {x y : A} (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hxy : Commute x y) :
    ‖x + I • y‖ ≤ √(‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [Real.le_sqrt (by positivity) (by positivity), hx.norm_add_I_smul_sq_of_commute hy hxy,
    ← hx.norm_mul_self, ← hy.norm_mul_self]
  exact norm_add_le ..

open Complex in
-- this lemma is poorly named, and maybe we should remove it entirely.
-- or else we could parametermize the lemma above with inequalities on `‖x‖` and `‖y‖`.
lemma _root_.IsSelfAdjoint.norm_isSelfAdjoint_add_I_smul_algebraMap
    {M : Type*} [CStarAlgebra M] {x : M} (hx : IsSelfAdjoint x)
    (hx₁ : ‖x‖ ≤ 1) (r : ℝ) :
    ‖x + I • algebraMap ℝ M r‖ ≤ √(1 + r ^ 2) := by
  nontriviality M
  apply hx.norm_add_I_smul_le_of_commute (.algebraMap M (.all r))
    (Algebra.commute_algebraMap_right r x) |>.trans
  simp only [norm_algebraMap', Real.norm_eq_abs, sq_abs]
  gcongr
  rwa [sq_le_one_iff₀ (by positivity)]

-- this lemma seems a bit too technical? Maybe it's useful though.
lemma _root_.IsSelfAdjoint.max_norm_add_sub_algebraMap_ge
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {x : A}
    (hx : IsSelfAdjoint x) (c : ℝ) (hc : c ∈ spectrum ℝ x) (r : ℝ) (hr : r ≥ 0) :
    |c| + r ≤ max ‖x + algebraMap ℝ A r‖ ‖x - algebraMap ℝ A r‖ := by
  obtain (hc' | hc') := le_total 0 c
  · apply le_max_of_le_left
    convert norm_apply_le_norm_cfc (fun y : ℝ ↦ y + r) x hc using 1
    · simp [abs_of_nonneg (a := c + r) (by positivity), abs_of_nonneg hc']
    · rw [cfc_add .., cfc_const .., cfc_id' ..]
  · apply le_max_of_le_right
    convert norm_apply_le_norm_cfc (fun y : ℝ ↦ -y + r) x hc using 1
    · rw [abs_of_nonpos hc', Real.norm_eq_abs, abs_of_nonneg]
      positivity [neg_nonneg.mpr hc']
    · rw [cfc_add _ (- ·) _, cfc_neg_id .., cfc_const .., norm_sub_rev]
      congr! 1
      abel

open Complex Filter in
/-- The selfadjoint elements are closed in the ultraweak topology. -/
lemma isClosed_setOf_isSelfAdjoint : IsClosed {x : σ(M, P) | IsSelfAdjoint x} := by
  nontriviality σ(M, P)
  have : Nontrivial M := linearEquiv ℂ M P |>.symm.nontrivial
  /- By the Krein-Smulian theorem, it suffices to show that the set of
  selfadjoint elements in the closed unit ball is closed. -/
  apply Ultraweak.krein_smulian_of_submodule <|
    (selfAdjoint.submodule ℝ σ(M, P)).restrictScalars ℝ≥0
  /- take any filter within the closed unit ball of selfadjoint elements which is
  also contained within `𝓝 x`. We must show `x` is in the closed unit ball of
  selfadjoint elements. This is the filter equivalent of "let x_α be a net of
  selfadjoint elements of norm at most 1 converging to x. We show x is selfadjoint." -/
  rw [isClosed_iff_forall_filter]
  intro x l hl_neBot hl_sa hlx
  refine Set.mem_inter (?_ : IsSelfAdjoint x) ?mem_ball
  -- Since the closed unit ball is ultraweakly closed, `x` is in the closed unit ball.
  case mem_ball =>
    exact isClosed_iff_forall_filter.mp (isClosed_closedBall  P (0 : M) 1)
      x l hl_neBot (by aesop) hlx
  /- To show `x` is self-adjoint, we show every element `c` of the `ℝ`-spectrum of
  `ℑ (ofUltraweak x)` is zero. -/
  refine .of_ofUltraweak ?_
  rw [← imaginaryPart_eq_zero_iff, ← ZeroMemClass.coe_eq_zero]
  refine CFC.eq_zero_of_spectrum_subset_zero _ (R := ℝ) (fun c hc ↦ ?_) (ℑ (ofUltraweak x)).2
    -- missing `cfc_tac` lemma for the last argument on the previous line
  rw [Set.mem_singleton_iff]
  rw [← abs_eq_zero]
  refine le_antisymm ?_ (abs_nonneg c)
  -- To show `c ≤ 0` It suffices to show `Tendsto (fun n : ℕ ↦ √(1 + n ^ 2) - n) atTop (𝓝 0)`
  refine ge_of_tendsto' (tendsto_sqrt_one_add_sq_sub_self_atTop.comp tendsto_natCast_atTop_atTop)
    fun n ↦ ?_
  /- By `IsSelfAdjoint.max_norm_add_sub_algebraMap_ge` it suffices to show that
  `‖ℑ x ± n‖ ≤ √(1 + n ^ 2)`. -/
  grw [Function.comp_apply, le_sub_iff_add_le,
    IsSelfAdjoint.max_norm_add_sub_algebraMap_ge (ℑ (ofUltraweak x)).2 c hc n (by positivity)]
  trans max ‖ofUltraweak x + I • algebraMap ℝ M n‖ ‖ofUltraweak x - I • algebraMap ℝ M n‖
  · apply max_le_max
    · convert imaginaryPart.norm_le (ofUltraweak x + I • algebraMap ℝ M n) using 1
      simp [IsSelfAdjoint.coe_realPart]
    · convert imaginaryPart.norm_le (ofUltraweak x - I • algebraMap ℝ M n) using 1
      simp [IsSelfAdjoint.coe_realPart]
  /- `fun m : σ(M, P) ↦ m + I • n` stays within the closed ball of radius `√(1 + n ^ 2)`
  and converges to `x + I • n` along the filter `l`. -/
  have h₃ (n : ℝ) : Tendsto (fun m : σ(M, P) ↦ m + I • algebraMap ℝ σ(M, P) n) l
      (𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) √(1 + n ^ 2)) ⊓
        𝓝 (x + I • algebraMap ℝ σ(M, P) n)) := by
    refine tendsto_inf.mpr ⟨.mono_left ?_ hl_sa, .add_const _ hlx⟩
    simpa using fun x hx hx_norm ↦
      hx.ofUltraweak.norm_isSelfAdjoint_add_I_smul_algebraMap hx_norm n
  apply max_le
  · have := isClosed_iff_forall_filter.mp <| isClosed_closedBall P (0 : M) (√(1 + n ^ 2))
    simpa using this _ _ inferInstance (tendsto_inf.mp (h₃ n) |>.1) (tendsto_inf.mp (h₃ n) |>.2)
  · have := isClosed_iff_forall_filter.mp <| isClosed_closedBall P (0 : M) (√(1 + n ^ 2))
    simpa [sub_eq_add_neg] using this _ _ inferInstance
      (by simpa only [even_two, Even.neg_pow] using (tendsto_inf.mp (h₃ (-n)) |>.1))
      (tendsto_inf.mp (h₃ (-n)) |>.2)

variable [PartialOrder M] [StarOrderedRing M]

--def Nonneg.nnrealSubmodule {α : Type*} [AddCommMonoid α] [Preorder α] [Module ℝ α]
    --[AddLeftMono α] [IsStrictOrderedModule ℝ α] :
    --Submodule ℝ≥0 α :=
  --{ carrier := {x : α | 0 ≤ x}
    --zero_mem' := le_rfl
    --add_mem' := add_nonneg
    --smul_mem' r _ h := smul_nonneg r.2 h }
--def Nonneg.nnrealSubmodule : Submodule ℝ≥0 σ(M, P) :=
  --{ carrier := {x : σ(M, P) | 0 ≤ x}
    --zero_mem' := le_rfl
    --add_mem' := add_nonneg
    --smul_mem' r _ h := smul_nonneg r.2 h }

--def Nonneg.convexCone :

open Pointwise in
/-- The nonnegative elements are closed in the ultraweak topology. -/
lemma isClosed_nonneg : IsClosed {x : σ(M, P) | 0 ≤ x} := by
  nontriviality σ(M, P)
  have : Nontrivial M := linearEquiv ℂ M P |>.symm.nontrivial
  set N := {x : σ(M, P) | 0 ≤ x}
  set S : Set σ(M, P) := ofUltraweak ⁻¹' (Metric.closedBall (0 : M) 1)
  set M_sa := {x : σ(M, P) | IsSelfAdjoint x}
  have h₁ : N ∩ S ⊆ (1 : σ(M, P)) +ᵥ M_sa ∩ S := by
    intro x ⟨hx_nonneg, hx_norm⟩
    refine ⟨x - 1, ⟨by aesop, ?_⟩, by simp⟩
    have := SpectrumRestricts.nnreal_iff_nnnorm (t := 1) hx_nonneg.isSelfAdjoint.ofUltraweak
      (by simpa [S] using hx_norm) |>.mp <| SpectrumRestricts.nnreal_of_nonneg hx_nonneg
    simpa [norm_sub_rev, S] using NNReal.coe_le_coe.mpr this
  have h₂ : (1 : σ(M, P)) +ᵥ M_sa ∩ S ⊆ N := by
    rintro - ⟨x, ⟨hx_sa, hx⟩, rfl⟩
    simp only [vadd_eq_add, Set.mem_setOf_eq, N]
    change 0 ≤ 1 + ofUltraweak x
    rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
      quasispectrumRestricts_iff_spectrumRestricts]
    refine ⟨by aesop, ?_⟩
    rw [SpectrumRestricts.nnreal_iff_nnnorm (t := 1 + 1)]
    · simpa using norm_sub_le .. |>.trans <| by simpa [S] using hx
    · aesop
    · exact norm_add_le .. |>.trans <| by simpa [S] using hx
  have h₃ : IsClosed ((1 : σ(M, P)) +ᵥ M_sa ∩ S) :=
    isClosed_setOf_isSelfAdjoint.inter (isClosed_closedBall P (0 : M) 1) |>.vadd _
  let N_submodule : Submodule ℝ≥0 σ(M, P) :=
    { carrier := N
      zero_mem' := by simp [N]
      add_mem' := add_nonneg
      smul_mem' r x hx := smul_nonneg r.2 hx }
  refine Ultraweak.krein_smulian_of_submodule N_submodule ?_
  change IsClosed (N ∩ S)
  convert h₃.inter (show IsClosed S from isClosed_closedBall P (0 : M) 1) using 1
  exact subset_antisymm (Set.subset_inter h₁ Set.inter_subset_right) (by gcongr)

instance : OrderClosedTopology σ(M, P) where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

end Ultraweak

open Ultraweak



--- none of what follows is necessary, but it should all go in Mathlib.

-- should be in Mathlib, quite trivial
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

@[simp]
theorem ker_imaginaryPart {E : Type*} [AddCommGroup E]
    [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E] :
    imaginaryPart.ker = selfAdjoint.submodule ℝ E := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

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
