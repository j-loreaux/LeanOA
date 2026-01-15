import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open scoped CStarAlgebra

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma inr_iff {p : A} :
    IsStarProjection p ↔ IsStarProjection (p : A⁺¹) := by
  simp [isStarProjection_iff]

protected alias ⟨inr, of_inr⟩ := inr_iff

variable [PartialOrder A] [StarOrderedRing A] {p q : A}

attribute [grind →] IsStarProjection.isSelfAdjoint
attribute [grind →] IsStarProjection.nonneg

lemma _root_.norm_star_mul_mul_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a) :
    ‖star b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_mul, (CFC.sqrt_nonneg a).star_eq,
    ← mul_assoc _ (CFC.sqrt a), mul_assoc _ _ (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a]

lemma _root_.IsSelfAdjoint.norm_mul_mul_self_of_nonneg {a : A} (b : A)
    (hb : IsSelfAdjoint b) (ha : 0 ≤ a) :
    ‖b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha

lemma _root_.norm_mul_mul_star_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a) :
    ‖b * a * star b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]

lemma _root_.IsSelfAdjoint.norm_mul_mul_self_of_nonneg' {a : A} (b : A)
    (hb : IsSelfAdjoint b) (ha : 0 ≤ a) :
    ‖b * a * b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

lemma sub_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
  List.TFAE
    [IsStarProjection (q - p),
    IsIdempotentElem (q - p),
    p ≤ q,
    q * p = p,
    p * q = p] := by
  tfae_have 1 ↔ 2 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_have 1 → 3 := fun h ↦ by simpa using h.nonneg
  tfae_have 3 → 4 := fun h ↦ by
    have key : p * (q - p) * p = 0 := by
      simp only [sub_mul, mul_sub, hp.isIdempotentElem.eq, sub_eq_zero]
      refine le_antisymm ?_ <| by
        simpa [hp.isIdempotentElem.eq] using conjugate_le_conjugate_of_nonneg h hp.nonneg
      have := by simpa [hp.inr.isIdempotentElem.eq, ← Unitization.inr_mul]
        using conjugate_le_conjugate_of_nonneg hq.inr.le_one hp.inr.nonneg
      rwa [← Unitization.inr_le_iff (p * q * p) p ?_ hp.isSelfAdjoint]
      exact hp.isSelfAdjoint.conjugate_nonneg hq.nonneg |>.isSelfAdjoint
    rw [← norm_eq_zero, hp.isSelfAdjoint.norm_mul_mul_self_of_nonneg _ (by simpa),
      sq_eq_zero_iff, norm_eq_zero] at key
    simpa [← mul_assoc, CFC.sqrt_mul_sqrt_self (q - p) (by simpa),
      sub_mul, sub_eq_zero, hp.isIdempotentElem.eq] using congr(CFC.sqrt (q - p) * $key)
  tfae_have 4 → 5 := fun h ↦ by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 5 → 1 := hp.sub_of_mul_eq_left hq
  tfae_finish

end IsStarProjection
