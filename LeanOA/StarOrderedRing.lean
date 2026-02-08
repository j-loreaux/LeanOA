import Mathlib.Analysis.Complex.Basic

-- Can go in `Algebra.Order.Star.Basic`
lemma IsSelfAdjoint.iff_of_le {R : Type*} [NonUnitalRing R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] {a b : R} (hab : a ≤ b) :
    IsSelfAdjoint a ↔ IsSelfAdjoint b := by
  replace hab := (sub_nonneg.mpr hab).isSelfAdjoint
  exact ⟨fun ha ↦ by simpa using hab.add ha, fun hb ↦ by simpa using (hab.sub hb).neg⟩

alias ⟨IsSelfAdjoint.of_ge, IsSelfAdjoint.of_le⟩ := IsSelfAdjoint.iff_of_le

open scoped ComplexStarModule

-- can go in `LinearAlgebra.Complex.Module`
namespace ComplexStarModule

variable {M : Type*} [AddCommGroup M] [StarAddMonoid M] [Module ℂ M] [StarModule ℂ M] {x y : M}

lemma ext (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x, ← realPart_add_I_smul_imaginaryPart y, h₁, h₂]

lemma ext_iff : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y := ⟨by grind, fun h ↦ ext h.1 h.2⟩

end ComplexStarModule

section StarOrderedRing

variable {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module ℂ A] [StarModule ℂ A]

lemma nonneg_iff_realPart_imaginaryPart {a : A} :
    0 ≤ a ↔ 0 ≤ ℜ a ∧ ℑ a = 0 := by
  refine ⟨fun h ↦ ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h ↦ ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using h.1

lemma le_iff_realPart_imaginaryPart {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} :
    a ≤ b ↔ ℜ a ≤ ℜ b ∧ ℑ a = ℑ b := by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using
    nonneg_iff_realPart_imaginaryPart (a := b - a)

lemma imaginaryPart_eq_of_le {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} (hab : a ≤ b) :
    ℑ a = ℑ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.2

lemma realPart_mono {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} (hab : a ≤ b) :
    ℜ a ≤ ℜ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.1

end StarOrderedRing
