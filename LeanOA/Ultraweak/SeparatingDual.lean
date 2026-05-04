module

public import LeanOA.Ultraweak.ContinuousStar
public import LeanOA.PositiveContinuousLinearMap
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

@[expose] public section

open scoped Ultraweak ComplexOrder ComplexStarModule

instance CFC.instSelfAdjointDecompose {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarRing A] [TopologicalSpace A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [PartialOrder A]
    [StarOrderedRing A] : SelfAdjointDecompose A where
  exists_nonneg_sub_nonnpos {a} ha :=
    ⟨a⁺, a⁻, CFC.posPart_nonneg a, CFC.negPart_nonneg a, (posPart_sub_negPart a ha).symm⟩

namespace Ultraweak

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

instance : StarHomClass (σ(M, P) →ₚ[ℂ] ℂ) σ(M, P) ℂ :=
  inferInstanceAs (StarHomClass (M →ₚ[ℂ] ℂ) M ℂ)

open Complex
set_option backward.isDefEq.respectTransparency false in
/-- If `a : σ(M, P)` is a selfadjoint element which is not nonnegative, then there is some
positive continuous linear functional which takes a negative value at `a`.

This is Sakai 1.7.2. Our approach is essentially the same, but instead of applying
Hahn-Banach to the `ℝ`-locally convex space of selfadjoint elements and then extending this
functional to `ℂ`-linear one defined everywhere, we apply it for `σ(M, P)` and then
precompose with the real part before extending to a `ℂ`-linear functional. -/
lemma exists_positiveCLM_apply_lt_zero (a : σ(M, P)) (ha₁ : IsSelfAdjoint a) (ha₂ : ¬ 0 ≤ a) :
    ∃ φ : σ(M, P) →P[ℂ] ℂ, φ a < 0 := by
  /- Since the nonnegative elements form a convex set, by the Hahn-Banach theorem,
  there is a continuous `ℝ`-linear functional `f` which separates them. Moreover,
  since the positive elements are an `ℝ`-convex cone, `f` must be nonnegative on
  nonnegative elements, so that `f a < 0`. -/
  have h₁ : Convex ℝ {x : σ(M, P) | 0 ≤ x} := ConvexCone.positive ℝ σ(M, P) |>.convex
  obtain ⟨f, u, hfa, hf⟩ := geometric_hahn_banach_point_closed h₁ Ultraweak.isClosed_nonneg ha₂
  have hu : u < 0 := map_zero f ▸ hf 0 le_rfl
  have hf_nonneg (x : σ(M, P)) (hx : 0 ≤ x) : 0 ≤ f x := by
    by_contra! hfx
    have : 0 < u * (f x)⁻¹ := mul_pos_of_neg_of_neg hu (inv_neg''.mpr hfx)
    simpa [hfx.ne] using hf _ (smul_nonneg this.le hx)
  replace hfa := hfa.trans hu
  clear u hu hf
  /- `g := x ↦ f (ℜ x)` is a continuous `ℝ`-linear functional, and we may extend
  it to a continuous `𝕜`-linear functional `φ := x ↦ f (ℜ x) + I • f (ℑ x)`. -/
  let g : StrongDual ℝ σ(M, P) := (2⁻¹ : ℝ) • (f + f ∘L (starL' ℝ (A := σ(M, P))))
  have hfg (x : σ(M, P)) : g x = f (ℜ x) := by simp [g, realPart_apply_coe]
  let φ : StrongDual ℂ σ(M, P) := g.extendRCLike
  have hφ (x : σ(M, P)) : φ x = f (ℜ x) + I • f (ℑ x) := by
    conv_lhs =>
      rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_smul]
      -- had to squeeze this because of an instance timeout
      simp only [StrongDual.extendRCLike_apply, hfg, selfAdjoint.realPart_coe, coe_algebraMap,
        RCLike.I_to_complex, realPart_I_smul, selfAdjoint.imaginaryPart_coe, neg_zero,
        ZeroMemClass.coe_zero, map_zero, ofReal_zero, ← smul_eq_mul, smul_zero, sub_zero, φ]
  have hφ_sa {x : σ(M, P)} (hx : IsSelfAdjoint x) : φ x = f x := by
    simp [hφ, hx.imaginaryPart, hx.coe_realPart]
  /- Since `f` is nonnegative and coincides with `φ` on selfadjoint elements,
  `φ` is the desired positive continuous linear map. -/
  use .mk₀ φ fun x hx ↦ by simpa [hφ_sa hx.isSelfAdjoint] using hf_nonneg x hx
  simpa [hφ_sa, ha₁]

instance : SelfAdjointDecompose σ(M, P) where
  exists_nonneg_sub_nonnpos {a} ha := by
    have ⟨_, _, _, _, key⟩ := ha.ofUltraweak.exists_nonneg_sub_nonpos
    replace key := by simpa using congr(toUltraweak ℂ P $key)
    exact ⟨_, _, by simpa, by simpa, key⟩

set_option backward.isDefEq.respectTransparency false in
lemma eq_zero_of_forall_positiveCLM (a : σ(M, P))
    (ha : ∀ φ : σ(M, P) →P[ℂ] ℂ, φ a = 0) :
    a = 0 := by
  suffices ∀ {a}, IsSelfAdjoint a → (∀ φ : σ(M, P) →P[ℂ] ℂ, φ a = 0) → a = 0 by
    have ⟨h₁, h₂⟩ := And.intro (this (ℜ a).2 (fun φ ↦ ?_)) (this (ℑ a).2 (fun φ ↦ ?_))
    · simpa [realPart_add_I_smul_imaginaryPart] using congr($h₁ + I • $h₂)
    · simp [φ.map_realPart, ha]
    · simp [φ.map_imaginaryPart, ha]
  intro a ha h
  have h₁ := by simpa using mt <| exists_positiveCLM_apply_lt_zero _ ha
  have h₂ := by simpa using mt <| exists_positiveCLM_apply_lt_zero _ ha.neg
  refine le_antisymm (h₂ ?_) (h₁ ?_)
  all_goals simp [h]

set_option backward.isDefEq.respectTransparency false in
lemma ext_positiveCLM {a b : σ(M, P)} (h : ∀ φ : σ(M, P) →P[ℂ] ℂ, φ a = φ b) :
    a = b :=
  sub_eq_zero.mp <| eq_zero_of_forall_positiveCLM _ fun φ ↦ by simp [h]

lemma ext_positiveCLM_iff {a b : σ(M, P)} :
    a = b ↔ ∀ φ : σ(M, P) →P[ℂ] ℂ, φ a = φ b :=
  ⟨by congr!, ext_positiveCLM⟩

end Ultraweak
