import Mathlib.Analysis.Complex.Basic

namespace Complex

open Metric in
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
