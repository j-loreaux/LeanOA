import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart

/-! # Expand API for `CFC.posPart`

[PR #19221](https://github.com/leanprover-community/mathlib4/pull/19221/) for most of it.
[PR #18056](https://github.com/leanprover-community/mathlib4/pull/18506) for the `span` results.

-/

open scoped NNReal

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

namespace CFC

@[simp]
lemma posPart_zero : (0 : A)⁺ = 0 := by simp [posPart_def]

@[simp]
lemma negPart_zero : (0 : A)⁻ = 0 := by simp [negPart_def]

section SMul

variable [StarModule ℝ A]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

@[simp]
lemma posPart_smul {r : ℝ≥0} {a : A} : (r • a)⁺ = r • a⁺ := by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul .., ← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx ↦ ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
    · have := (not_iff_not.mpr <| (IsSelfAdjoint.all r).smul_iff hr.isUnit (x := a)) |>.mpr ha
      simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha,
        cfcₙ_apply_of_not_predicate _ this]

@[simp]
lemma negPart_smul {r : ℝ≥0} {a : A} : (r • a)⁻ = r • a⁻ := by
  simpa using posPart_smul (r := r) (a := -a)

lemma posPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁺ = r • a⁺ :=
  posPart_smul (r := ⟨r, hr⟩)

lemma posPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁺ = -r • a⁻ := by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul, ← smul_neg, posPart_smul_of_nonneg (neg_nonneg.mpr hr), posPart_neg]

lemma negPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁻ = r • a⁻ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]

lemma negPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁻ = -r • a⁺ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

end SMul

variable [PartialOrder A] [StarOrderedRing A]

lemma posPart_eq_of_eq_sub_negPart {a b : A} (hab : a = b - a⁻) (hb : 0 ≤ b := by cfc_tac) :
    a⁺ = b := by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab

lemma negPart_eq_of_eq_PosPart_sub {a c : A} (hac : a = a⁺ - c) (hc : 0 ≤ c := by cfc_tac) :
    a⁻ = c := by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac

lemma le_posPart {a : A} (ha : IsSelfAdjoint a) : a ≤ a⁺ := by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)

lemma neg_negPart_le {a : A} (ha : IsSelfAdjoint a) : -a⁻ ≤ a := by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

variable [NonnegSpectrumClass ℝ A]

lemma posPart_eq_self (a : A) : a⁺ = a ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_rhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx ↦ ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

lemma negPart_eq_neg (a : A) : a⁻ = -a ↔ a ≤ 0 := by
  rw [← neg_inj, neg_neg, eq_comm]
  refine ⟨fun ha ↦ by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha ↦ ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def, ← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id ℝ a]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Unitization.quasispectrum_eq_spectrum_inr ℝ, ← neg_neg x, ← Set.mem_neg,
    spectrum.neg_eq, ← Unitization.inr_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ] at hx
  rw [← neg_eq_iff_eq_neg, eq_comm]
  simpa using quasispectrum_nonneg_of_nonneg _ ha _ hx

end CFC

end NonUnital

section Unital

namespace CFC

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

@[simp]
lemma posPart_one : (1 : A)⁺ = 1 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma negPart_one : (1 : A)⁻ = 0 := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma posPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁺ = algebraMap ℝ A r⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
lemma negPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁻ = algebraMap ℝ A r⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

open NNReal in
@[simp]
lemma posPart_algebraMap_nnreal (r : ℝ≥0) : (algebraMap ℝ≥0 A r)⁺ = algebraMap ℝ≥0 A r := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, IsScalarTower.algebraMap_apply ℝ≥0 ℝ A]
  simp

open NNReal in
@[simp]
lemma posPart_natCast (n : ℕ) : (n : A)⁺ = n := by
  rw [← map_natCast (algebraMap ℝ≥0 A), posPart_algebraMap_nnreal]

end CFC

end Unital


section SpanNonneg

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
variable [StarRing A] [TopologicalSpace A] [StarModule ℂ A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [PartialOrder A] [StarOrderedRing A]

open Submodule Complex
open scoped ComplexStarModule

lemma CStarAlgebra.linear_combination_nonneg (x : A) :
    ((ℜ x : A)⁺ - (ℜ x : A)⁻) + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) = x := by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2, ← smul_sub, CFC.posPart_sub_negPart _ (ℑ x).2,
    realPart_add_I_smul_imaginaryPart x]

/-- A C⋆-algebra is spanned by its nonnegative elements. -/
lemma CStarAlgebra.span_nonneg : Submodule.span ℂ {a : A | 0 ≤ a} = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

end SpanNonneg
