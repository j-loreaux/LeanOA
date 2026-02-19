import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

open Complex ComplexStarModule

lemma cfcₙ_re_id {A : Type*} [NonUnitalCStarAlgebra A] {a : A} [IsStarNormal a] :
    cfcₙ (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

lemma cfcₙ_im_id {A : Type*} [NonUnitalCStarAlgebra A] {a : A} [IsStarNormal a] :
    cfcₙ (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfcₙ (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add .., cfcₙ_const_mul .., cfcₙ_re_id] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

lemma cfc_re_id {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a] :
    cfc (re · : ℂ → ℂ) a = ℜ a := by rw [← cfcₙ_eq_cfc, cfcₙ_re_id]

lemma cfc_im_id {A : Type*} [CStarAlgebra A] {a : A} [IsStarNormal a] :
    cfc (im · : ℂ → ℂ) a = ℑ a := by rw [← cfcₙ_eq_cfc, cfcₙ_im_id]
