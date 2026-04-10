import LeanOA.Corner
import LeanOA.CFC
import LeanOA.Ultraweak.OrderClosed
import LeanOA.Ultraweak.ContinuousStar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

section RealImaginaryPart

open scoped ComplexStarModule

variable {M : Type*} [AddCommGroup M] [StarAddMonoid M] [Module ℂ M] [StarModule ℂ M]
    [TopologicalSpace M] [ContinuousSMul ℂ M] [ContinuousStar M] [IsTopologicalAddGroup M]

@[fun_prop]
lemma continuous_realPart : Continuous (ℜ : M → selfAdjoint M) := by
  simp_rw [continuous_induced_rng, Function.comp_def, realPart_apply_coe]
  fun_prop

@[fun_prop]
lemma continuous_imaginaryPart : Continuous (ℑ : M → selfAdjoint M) := by
  simp_rw [continuous_induced_rng, Function.comp_def, imaginaryPart_apply_coe]
  fun_prop

end RealImaginaryPart

variable {M P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [Predual ℂ M P]

open NonUnitalStarSubalgebra Metric Ultraweak Set
open scoped Ultraweak NNReal

lemma IsStarProjection.mem_image_mul_mul_nonnegative_inter_unitClosedBall_iff
    {e : M} (he : IsStarProjection e) :
    (e * · * e) '' ({x | 0 ≤ x} ∩ closedBall 0 1) = Icc 0 e ∩ closedBall 0 1 := by
  ext x
  constructor
  · rintro ⟨x, ⟨hx₀, hx₁⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [mem_closedBall, dist_zero_right] at hx₁ ⊢
    · exact he.isSelfAdjoint.conjugate_nonneg hx₀
    · calc
        e * x * e ≤ ‖x‖ • (e * e) := by
          rw (occs := [1,3]) [← he.isSelfAdjoint.star_eq]
          exact CStarAlgebra.star_left_conjugate_le_norm_smul hx₀.isSelfAdjoint
        _ ≤ (1 : ℝ) • e := by
          grw [he.isIdempotentElem.eq, hx₁]
          exact he.nonneg
        _ = e := by simp
    · grw [norm_mul₃_le, hx₁, he.norm_le]
      simp
  · rintro ⟨⟨hx₀, hxe⟩, hx₁⟩
    exact ⟨x, ⟨hx₀, hx₁⟩, he.conjugate_of_nonneg_of_le hx₀ hxe⟩

open CStarAlgebra in
lemma isSelfAdjoint_and_norm_le_iff {x : M} {r : ℝ} :
    IsSelfAdjoint x ∧ ‖x‖ ≤ r ↔ ∃ y z, (0 ≤ y ∧ ‖y‖ ≤ r) ∧ (0 ≤ z ∧ ‖z‖ ≤ r) ∧ x = y - z := by
  constructor
  · rintro ⟨hx, hxr⟩
    exact ⟨x⁺, x⁻,
      ⟨by cfc_tac, (norm_posPart_le x).trans hxr⟩,
      ⟨by cfc_tac, (norm_negPart_le x).trans hxr⟩,
      (CFC.posPart_sub_negPart _ hx).symm⟩
  · rintro ⟨y, z, ⟨hy, hyr⟩, ⟨hz, hzr⟩, rfl⟩
    refine ⟨by cfc_tac, ?_⟩
    grw [hz.isSelfAdjoint.neg.norm_le_max_of_le_of_le (c := y), hyr, norm_neg, hzr, max_self]
    all_goals simpa

open CStarAlgebra in
lemma isSelfAdjoint_and_norm_lt_iff {x : M} {r : ℝ} :
    IsSelfAdjoint x ∧ ‖x‖ < r ↔ ∃ y z, (0 ≤ y ∧ ‖y‖ < r) ∧ (0 ≤ z ∧ ‖z‖ < r) ∧ x = y - z := by
  constructor
  · rintro ⟨hx, hxr⟩
    exact ⟨x⁺, x⁻,
      ⟨by cfc_tac, (norm_posPart_le x).trans_lt hxr⟩,
      ⟨by cfc_tac, (norm_negPart_le x).trans_lt hxr⟩,
      (CFC.posPart_sub_negPart _ hx).symm⟩
  · rintro ⟨y, z, ⟨hy, hyr⟩, ⟨hz, hzr⟩, rfl⟩
    refine ⟨by cfc_tac, ?_⟩
    grw [hz.isSelfAdjoint.neg.norm_le_max_of_le_of_le (c := y) (by simpa) (by simpa)]
    simp_all

open Pointwise in
lemma setOf_isSelfAdjoint_inter_closedBall_eq {r : ℝ} :
    {x : M | IsSelfAdjoint x} ∩ closedBall 0 r =
      {x | 0 ≤ x} ∩ closedBall 0 r - {x | 0 ≤ x} ∩ closedBall 0 r := by
  ext
  simp [isSelfAdjoint_and_norm_le_iff, Set.mem_sub]
  grind

open Pointwise in
lemma setOf_isSelfAdjoint_inter_ball_eq {r : ℝ} :
    {x : M | IsSelfAdjoint x} ∩ ball 0 r =
      {x | 0 ≤ x} ∩ ball 0 r - {x | 0 ≤ x} ∩ ball 0 r := by
  ext
  simp [isSelfAdjoint_and_norm_lt_iff, Set.mem_sub]
  grind

open Pointwise in
-- the proof of this is inlined in the theorem below.
example (e : M) :
    letI S := closedBall 0 1
    letI Ms := {x | IsSelfAdjoint x}
    letI P := {x | 0 ≤ x}
    (e * · * e) '' (Ms ∩ S) = (e * · * e) '' (P ∩ S) - (e * · * e) '' (P ∩ S) := by
  have e_mul_e : (e * · * e) = LinearMap.mulLeftRight ℂ ⟨e, e⟩ := by ext; simp
  rw [e_mul_e, ← Set.image_sub, setOf_isSelfAdjoint_inter_closedBall_eq]

lemma IsStarProjection.idempotent_mul_mul {M : Type*} [Semigroup M] [StarMul M]
    {e : M} (he : IsStarProjection e) :
    (e * · * e) ∘ (e * · * e) = (e * · * e) := by
  ext; simp [mul_assoc, he.isIdempotentElem.mul_mul_self, he.isIdempotentElem.mul_self_mul]

/-- If `f` is an idempotent function which maps sets `s` and `t` to themselves, then
`f '' (s ∩ t) = (f '' s) ∩ t`. -/
lemma Set.MapsTo.image_inter_of_idempotent {α : Type*} {s t : Set α} {f : α → α}
    (hf : f ∘ f = f) (hfs : MapsTo f s s) (hft : MapsTo f t t) :
    f '' (s ∩ t) = (f '' s) ∩ t := by
  apply subset_antisymm (fun _ _ ↦ by aesop)
  rintro - ⟨⟨x, hx, rfl⟩, hxt⟩
  exact ⟨f x, ⟨hfs hx, hxt⟩, congr($hf x)⟩

open scoped ComplexStarModule Pointwise in
open Filter in
lemma IsStarProjection.isClosed_corner_of_ultraweak {e : σ(M, P)} (he : IsStarProjection e) :
    IsClosed (corner ℂ e : Set σ(M, P)) := by
  apply Ultraweak.krein_smulian_of_submodule ((corner ℂ e).toSubmodule.restrictScalars ℝ≥0)
  simp only [Submodule.coe_restrictScalars, Submodule.coe_set_mk,
    NonUnitalSubsemiring.coe_toAddSubmonoid, NonUnitalSubalgebra.coe_toNonUnitalSubsemiring,
    coe_toNonUnitalSubalgebra, corner_carrier, he.isSelfAdjoint.star_eq]
  set B := closedBall (0 : M) 1
  suffices IsClosed ((e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B) by
    rw [isClosed_iff_forall_filter] at this ⊢
    intro x l hl_neBot hl hlx
    obtain ⟨⟨y, -, hxy⟩, -⟩ := this (ℜ x : σ(M, P)) (map ((ℜ ·) : σ(M, P) → σ(M, P)) l)
      inferInstance
      (by
        simp only [le_principal_iff, Filter.mem_map] at hl ⊢
        filter_upwards [hl] with m hm
        obtain ⟨⟨x, rfl⟩, hx⟩ := hm
        simp only [Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image,
          Set.mem_setOf_eq, mem_closedBall, dist_zero_right, B] at hx ⊢
        refine ⟨⟨ℜ x, (ℜ x).2, ?_⟩, realPart.norm_le _ |>.trans hx⟩
        simp [realPart_apply_coe, ← mul_assoc, he.isSelfAdjoint.star_eq, mul_add, add_mul])
      (by grw [hlx]; apply Continuous.tendsto; fun_prop)
    obtain ⟨⟨z, -, hxz⟩, -⟩ := this (ℑ x : σ(M, P)) (map ((ℑ ·) : σ(M, P) → σ(M, P)) l)
      inferInstance
      (by
        simp only [le_principal_iff, Filter.mem_map] at hl ⊢
        filter_upwards [hl] with m hm
        obtain ⟨⟨x, rfl⟩, hx⟩ := hm
        simp only [Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image,
          Set.mem_setOf_eq, mem_closedBall, dist_zero_right, B] at hx ⊢
        refine ⟨⟨ℑ x, (ℑ x).2, ?_⟩, imaginaryPart.norm_le _ |>.trans hx⟩
        simp [imaginaryPart_apply_coe, ← mul_assoc, he.isSelfAdjoint.star_eq, mul_sub, sub_mul])
      (by grw [hlx]; apply Continuous.tendsto; fun_prop)
    refine ⟨⟨y + Complex.I • z, ?_⟩, ?_⟩
    · simp [mul_add, add_mul, hxy, hxz, realPart_add_I_smul_imaginaryPart]
    · exact isClosed_iff_forall_filter.mp (Ultraweak.isClosed_closedBall ℂ P 0 1) x l hl_neBot
        (by grw [hl]; simp [B]) hlx
  suffices (e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B =
      (· - ·).uncurry '' (Icc 0 e ∩ ofUltraweak ⁻¹' B) ×ˢ (Icc 0 e ∩ ofUltraweak ⁻¹' B) by
    refine this ▸ (IsCompact.image ?_ continuous_sub |>.isClosed)
    suffices h : IsCompact (Icc 0 e ∩ ofUltraweak ⁻¹' B) from h.prod h
    exact (Ultraweak.isCompact_closedBall ℂ P 0 1).inter_left isClosed_Icc
  calc (e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B
    _ = (e * · * e) '' ({x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B) := by
      apply Eq.symm <| Set.MapsTo.image_inter_of_idempotent he.idempotent_mul_mul
        (fun x hx ↦ by simpa [he.isSelfAdjoint.star_eq] using hx.conjugate e) (fun x hx ↦ ?_)
      simp only [mem_preimage, mem_closedBall, dist_zero_right, ofUltraweak_mul, B] at hx ⊢
      grw [norm_mul₃_le, hx, he.norm_le, mul_one, mul_one]
    _ = ofUltraweak ⁻¹' ((ofUltraweak e * · * ofUltraweak e) '' ({x | IsSelfAdjoint x} ∩ B)) := rfl
    _ = ofUltraweak ⁻¹' (Icc 0 (ofUltraweak e) ∩ B - Icc 0 (ofUltraweak e) ∩ B) := by
      have he' : IsStarProjection (ofUltraweak e) := he
      have e_mul_e : (ofUltraweak e * · * ofUltraweak e) =
          LinearMap.mulLeftRight ℂ ⟨ofUltraweak e, ofUltraweak e⟩ := by ext; simp
      rw [← he'.mem_image_mul_mul_nonnegative_inter_unitClosedBall_iff, e_mul_e,
        setOf_isSelfAdjoint_inter_closedBall_eq, Set.image_sub]
    _ = _ := by rw [← Set.image2_sub, ← Set.image_uncurry_prod]; rfl
