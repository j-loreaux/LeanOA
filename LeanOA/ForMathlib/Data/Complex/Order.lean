import Mathlib.Analysis.Complex.Order

namespace Complex

lemma norm_le_re_iff_eq_norm {z : ℂ} :
    ‖z‖ ≤ z.re ↔ z = ‖z‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · replace h : z.re = ‖z‖ := le_antisymm (re_le_norm z) h
    apply ext
    · simp [h]
    · rw [re_eq_norm, nonneg_iff] at h
      simpa using h.2.symm
  · rw [h]
    simp

lemma re_le_neg_norm_iff_eq_neg_norm {z : ℂ} :
    z.re ≤ -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

lemma norm_le_im_iff_eq_I_mul_norm {z : ℂ} :
    ‖z‖ ≤ z.im ↔ z = I * ‖z‖ := by
  have := norm_le_re_iff_eq_norm (z := -I * z)
  simp only [Complex.norm_mul, norm_neg, norm_I, one_mul, mul_re, neg_re, I_re,
    neg_zero, zero_mul, neg_im, I_im, zero_sub, ← neg_mul, neg_neg] at this
  rw [this, ← smul_eq_mul, eq_comm, ← inv_smul_eq_iff₀ (by simp)]
  simp [eq_comm]

lemma im_le_neg_norm_iff_eq_neg_I_mul_norm {z : ℂ} :
    z.im ≤ -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

end Complex
