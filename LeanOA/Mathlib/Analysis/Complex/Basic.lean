import Mathlib.Analysis.Complex.Basic

namespace Complex

open Metric in
set_option backward.isDefEq.respectTransparency false in
/-- A subset of circle centered at the origin in `ℂ` of radius `r` is a subset of
the `slitPlane` if it does not contain `-r`. -/
lemma subset_slitPlane_of_subset_sphere {r : ℝ} {s : Set ℂ} (hs : s ⊆ sphere 0 r)
      (hr : (-r : ℂ) ∉ s) :
      s ⊆ slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff_not_le_zero]
  by_contra! h
  have ⟨_, h_im⟩ := h
  apply hr
  convert hz
  rw [← Complex.re_eq_neg_norm] at h
  rw [← Complex.re_add_im z, h_im, h]
  simpa using (hs hz).symm

end Complex

open scoped ComplexStarModule

section StarOrderedRing

variable {A : Type*} [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module ℂ A] [StarModule ℂ A]

lemma nonneg_iff_realPart_imaginaryPart {a : A} :
    0 ≤ a ↔ 0 ≤ ℜ a ∧ ℑ a = 0 := by
  refine ⟨fun h ↦ ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h ↦ ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using h.1

set_option backward.isDefEq.respectTransparency false in
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
