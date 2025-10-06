import Mathlib.Analysis.Complex.Norm

namespace Complex

lemma norm_sub_one_sq_eq_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm, normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring

open Metric in
lemma norm_sub_one_sq_eqOn_sphere :
    (sphere (0 : ℂ) 1).EqOn (‖· - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
  fun z hz ↦ norm_sub_one_sq_eq_of_norm_one (by simpa using hz)

end Complex
