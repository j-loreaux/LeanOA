module

public import LeanOA.Corner
public import LeanOA.CFC
public import LeanOA.Mathlib.Algebra.Group.Idempotent
public import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import LeanOA.Mathlib.Data.Set.Function
public import LeanOA.Ultraweak.OrderClosed
public import LeanOA.Ultraweak.ContinuousStar

@[expose] public section

variable {M P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [Predual ℂ M P]

open NonUnitalStarSubalgebra Metric Ultraweak Set
open scoped Ultraweak NNReal

open Pointwise in
-- the proof of this is inlined in the theorem below.
example (e : M) :
    letI S := closedBall 0 1
    letI Ms := {x | IsSelfAdjoint x}
    letI P := {x | 0 ≤ x}
    (e * · * e) '' (Ms ∩ S) = (e * · * e) '' (P ∩ S) - (e * · * e) '' (P ∩ S) := by
  have e_mul_e : (e * · * e) = LinearMap.mulLeftRight ℂ ⟨e, e⟩ := rfl
  rw [e_mul_e, ← Set.image_sub, setOf_isSelfAdjoint_inter_closedBall_eq]

open scoped ComplexStarModule Pointwise in
lemma IsStarProjection.isClosed_corner_of_ultraweak {e : σ(M, P)} (he : IsStarProjection e) :
    IsClosed (corner ℂ e : Set σ(M, P)) := by
  /- By the Krein–Smulian theorem, it suffices to prove that the corner intersected with the
  closed unit ball is closed.

  Letting `B := closedBall 0 1`, `Ms := {x | IsSelfAdjoint x}` and `P := {x | 0 ≤ x}`, the
  sketch of the full argument is as follows. We must show `((e * · * e) '' M) ∩ S` is
  ultraweakly closed, but it suffices to restrict to selfadjoint elements and show that
  `((e * · * e) '' Ms) ∩ S` is ultraweakly closed. We have the following chain of inequalities:
  ```lean
  calc ((e * · * e) '' Ms) ∩ S = (e * · * e) '' (Ms ∩ S)
    _ = (e * · * e) '' (P ∩ S) - (e * · * e) '' (P ∩ S)
    _ = Icc 0 e ∩ S - Icc 0 e ∩ S
  ```
  Since subtraction is continuous, `S` is ultraweakly compact and `Icc 0 e` is closed, this is
  the continuous image of a compact set, and therefore closed. -/
  apply Ultraweak.krein_smulian_of_submodule ((corner ℂ e).toSubmodule.restrictScalars ℝ≥0)
  simp only [Submodule.coe_restrictScalars, Submodule.coe_set_mk,
    NonUnitalSubsemiring.coe_toAddSubmonoid, NonUnitalSubalgebra.coe_toNonUnitalSubsemiring,
    coe_toNonUnitalSubalgebra, corner_carrier, he.isSelfAdjoint.star_eq]
  set B := closedBall (0 : M) 1
  /- Since `star` is continuous, and hence so are `ℜ` and `ℑ`, it suffices to show that the
  selfadjoint part of the corner intersected with the closed unit ball is closed. -/
  suffices hS : IsClosed ((e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B) by
    have hmapsTo (f : σ(M, P) → σ(M, P)) (hsa : ∀ y : σ(M, P), IsSelfAdjoint (f y))
        (hcomm : ∀ y : σ(M, P), f (e * y * e) = e * f y * e)
        (hnorm : ∀ y : σ(M, P), ‖ofUltraweak (f y)‖ ≤ ‖ofUltraweak y‖) :
        MapsTo f ((range fun x ↦ e * x * e) ∩ ofUltraweak ⁻¹' B)
          ((e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B) := by
      rintro - ⟨⟨y, rfl⟩, hy⟩
      simp only [mem_preimage, mem_closedBall, dist_zero_right, B] at hy
      exact ⟨⟨f y, hsa y, (hcomm y).symm⟩, by simpa [B] using (hnorm _).trans hy⟩
    refine isClosed_of_closure_subset fun x hx ↦ ?_
    obtain ⟨⟨y, -, hxy⟩, -⟩ := hmapsTo (ℜ ·) (by simp)
        (by simp [realPart_apply_coe, ← mul_assoc, he.isSelfAdjoint.star_eq, mul_add, add_mul])
        (fun y ↦ by simpa using realPart.norm_le (ofUltraweak y))
        |>.closure_left (by fun_prop) hS hx
    obtain ⟨⟨z, -, hxz⟩, -⟩ := hmapsTo (ℑ ·) (by simp)
        (fun y ↦ by simp [imaginaryPart_apply_coe, ← mul_assoc, he.isSelfAdjoint.star_eq,
          mul_sub, sub_mul])
        (fun y ↦ by simpa using imaginaryPart.norm_le (ofUltraweak y))
        |>.closure_left (by fun_prop) hS hx
    refine ⟨⟨y + Complex.I • z, ?_⟩, ?_⟩
    · simp [mul_add, add_mul, hxy, hxz, realPart_add_I_smul_imaginaryPart]
    · exact (Ultraweak.isClosed_closedBall ℂ P 0 1).closure_subset_iff.mpr inter_subset_right hx
  /- It suffices to show that every selfadjoint element in the corner inside the unit ball
  coincides with a difference of nonnegative elements in the corner in the unit ball. Indeed,
  since such a nonnegative element `x = e * a * e`, so `0 ≤ x ≤ e`, and since `Set.Icc 0 e` is
  closed, the set in question is the image of a compact set under a continuous map (subtraction)
  and is therefore compact, hence closed. -/
  suffices (e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B =
      (· - ·).uncurry '' (Icc 0 e ∩ ofUltraweak ⁻¹' B) ×ˢ (Icc 0 e ∩ ofUltraweak ⁻¹' B) by
    refine this ▸ (IsCompact.image ?_ continuous_sub |>.isClosed)
    suffices h : IsCompact (Icc 0 e ∩ ofUltraweak ⁻¹' B) from h.prod h
    exact (Ultraweak.isCompact_closedBall ℂ P 0 1).inter_left isClosed_Icc
  /- Compression by `e` is idempotent and maps the set of selfadjoint elements, and the closed
  unit ball, to themselves. Therefore, the selfadjoint part of the corner intersected with
  the closed unit ball coincides with the corner of the selfadjoint part of the closed unit ball.
  That is, `‖e * x * e‖ ≤ 1` with `star x = x` if and only if there is some `‖y‖ ≤ 1` with
  `star y = y` such that `e * y * e = e * x * e`. -/
  calc (e * · * e) '' {x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B
    _ = (e * · * e) '' ({x | IsSelfAdjoint x} ∩ ofUltraweak ⁻¹' B) := by
      apply Eq.symm <| Set.MapsTo.image_inter_of_idempotent he.isIdempotentElem.idempotent_mul_mul
        (fun x hx ↦ by simpa [he.isSelfAdjoint.star_eq] using hx.conjugate e) (fun x hx ↦ ?_)
      simp only [mem_preimage, mem_closedBall, dist_zero_right, ofUltraweak_mul, B] at hx ⊢
      grw [norm_mul₃_le, hx, he.norm_le]
      simpa using he.norm_le
    /- We can shift this over from the type synonym `σ(M, P)` to `M`, and then use the fact that
    `{x | IsSelfAdjoint x} ∩ B = {x | 0 ≤ x} ∩ B - {x | 0 ≤ x} ∩ B` since `M` is a C⋆-algebra. -/
    _ = ofUltraweak ⁻¹' ((ofUltraweak e * · * ofUltraweak e) '' ({x | IsSelfAdjoint x} ∩ B)) := rfl
    _ = ofUltraweak ⁻¹' (Icc 0 (ofUltraweak e) ∩ B - Icc 0 (ofUltraweak e) ∩ B) := by
      have he' : IsStarProjection (ofUltraweak e) := he
      have e_mul_e : (ofUltraweak e * · * ofUltraweak e) =
          LinearMap.mulLeftRight ℂ ⟨ofUltraweak e, ofUltraweak e⟩ := by ext; simp
      rw [← he'.mem_image_mul_mul_nonneg_inter_unitClosedBall_iff, e_mul_e,
        setOf_isSelfAdjoint_inter_closedBall_eq, Set.image_sub]
    _ = _ := by rw [← Set.image2_sub, ← Set.image_uncurry_prod]; rfl
