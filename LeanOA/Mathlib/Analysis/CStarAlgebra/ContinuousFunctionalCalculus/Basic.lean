import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

open Complex ComplexStarModule

variable {A : Type*} {p : A → Prop} [TopologicalSpace A]

section nonUnital
variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [NonUnitalContinuousFunctionalCalculus ℂ A p]

lemma cfcₙ_re_id (a : A) (hp : p a := by cfc_tac) :
    cfcₙ (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

lemma cfcₙ_im_id (a : A) (hp : p a := by cfc_tac) :
    cfcₙ (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfcₙ (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add .., cfcₙ_const_mul .., cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

end nonUnital

section unital
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ A p]
  [ContinuousMapZero.UniqueHom ℂ A]

lemma cfc_re_id (a : A) (hp : p a := by cfc_tac) :
    cfc (re · : ℂ → ℂ) a = ℜ a := by rw [← cfcₙ_eq_cfc, cfcₙ_re_id a]

lemma cfc_im_id (a : A) (hp : p a := by cfc_tac) :
    cfc (im · : ℂ → ℂ) a = ℑ a := by rw [← cfcₙ_eq_cfc, cfcₙ_im_id a]

end unital
