module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Lemmas
public import LeanOA.Mathlib.Tactic.CFCSimp.Attr

/-!
# The `@[cfc_simp]` lemma set

The same lemmas, with the same priorities, as the `@[cfc_pull]` set in `CFCPull/Tags.lean`; see
there for what is deliberately absent, and why.
-/

public section

open scoped NNReal

attribute [cfc_simp] cfc_id' cfcₙ_id'

attribute [cfc_simp] cfcₙ_eq_cfc

attribute [cfc_simp]
  cfc_nnreal_eq_real cfcₙ_nnreal_eq_real cfc_real_eq_complex cfcₙ_real_eq_complex
  cfc_real_eq_nnreal cfcₙ_real_eq_nnreal cfc_complex_eq_real cfcₙ_complex_eq_real

attribute [cfc_simp]
  cfc_add cfc_sub cfc_neg cfc_mul cfc_pow cfc_smul cfc_star
  cfc_const cfc_const_one cfc_const_zero cfc_const_add cfc_add_const
  cfc_inv cfc_inv_id cfc_zpow cfc_ringInverse_id cfc_map_div
  cfc_map_polynomial cfc_polynomial
  cfc_neg_id cfc_pow_id cfc_smul_id cfc_star_id
  cfc_eq_cfcL cfc_apply_mkD cfc_eq_cfcL_mkD cfcHom_eq_cfc_extend_zero

attribute [cfc_simp 1100] cfc_const_mul cfc_const_mul_id

attribute [cfc_simp]
  cfcₙ_add cfcₙ_sub cfcₙ_neg cfcₙ_mul cfcₙ_smul cfcₙ_star cfcₙ_const_zero
  cfcₙ_neg_id cfcₙ_smul_id cfcₙ_star_id
  cfcₙ_eq_cfcₙL cfcₙ_apply_mkD cfcₙ_eq_cfcₙL_mkD cfcₙHom_eq_cfcₙ_extend_zero

attribute [cfc_simp 1100] cfcₙ_const_mul cfcₙ_const_mul_id

attribute [cfc_simp] cfc_sum cfcₙ_sum

attribute [cfc_simp]
  CFC.posPart_def CFC.negPart_def
  CFC.sqrt_def CFC.sqrt_eq_cfc CFC.sqrt_eq_real_sqrt CFC.abs_def
  CFC.nnrpow_def CFC.rpow_def CFC.rpow_eq_cfc_real
  CFC.log_def CFC.exp_eq_normedSpace_exp
  cfc_re_id cfc_im_id cfcₙ_re_id cfcₙ_im_id
  Matrix.IsHermitian.cfc_eq
  Unitization.complex_cfcₙ_eq_cfc_inr Unitization.real_cfcₙ_eq_cfc_inr
  Unitization.nnreal_cfcₙ_eq_cfc_inr

attribute [cfc_simp 1100] CFC.real_exp_eq_normedSpace_exp CFC.complex_exp_eq_normedSpace_exp

attribute [cfc_simp 900] cfc_tsub cfcₙ_tsub

attribute [cfc_simp] StarAlgHom.map_cfc NonUnitalStarAlgHom.map_cfcₙ

attribute [cfc_simp 900] StarAlgHomClass.map_cfc NonUnitalStarAlgHomClass.map_cfcₙ

attribute [cfc_simp]
  cfc_comp' cfcₙ_comp'
  cfc_comp_pow cfc_comp_smul cfc_comp_star cfc_comp_neg cfc_comp_inv cfc_comp_zpow
  cfcₙ_comp_smul cfcₙ_comp_star cfcₙ_comp_neg
  cfc_comp_norm
  cfc_realPart cfc_imaginaryPart cfcₙ_realPart cfcₙ_imaginaryPart

attribute [cfc_simp 1100]
  cfc_comp_const_mul cfcₙ_comp_const_mul
  cfc_real_comp_norm cfcₙ_real_comp_norm
  cfc_complex_comp_norm cfcₙ_complex_comp_norm
