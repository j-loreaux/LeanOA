module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Lemmas
public import LeanOA.Mathlib.Tactic.CFCPull.Attr

/-!
# The `@[cfc_pull]` lemma set

This tags all the lemmas currently used by the `cfc_pull` tactic. We do it in a central location
for convenience for now, but upon upstreaming to Mathlib these should be distributed.
For lemmas which are deliberately absent, we explain the reason.
-/

public section

open scoped NNReal

/-! ### Identity

The lemmas that say the calculus applied to the identity function is the element itself. -/

attribute [cfc_pull] cfc_id' cfcₙ_id'

/-! ### Unitality

The bridge from the non-unital calculus to the unital one, used whenever a `cfcₙ` shows up in a
goal that asks for a `cfc`, and conversely. -/

attribute [cfc_pull] cfcₙ_eq_cfc

/-! ### Scalars

Widening (`ℝ≥0 → ℝ → ℂ`) and narrowing (`ℂ → ℝ → ℝ≥0`) conversions. The four narrowing lemmas
carry a hypothesis the tactic cannot read off the syntax, which comes back as a `cfc_pull.side`
goal; they are tagged all the same, so that any two of the three rings are reachable from one
another. -/

attribute [cfc_pull]
  cfc_nnreal_eq_real cfcₙ_nnreal_eq_real cfc_real_eq_complex cfcₙ_real_eq_complex
  cfc_real_eq_nnreal cfcₙ_real_eq_nnreal cfc_complex_eq_real cfcₙ_complex_eq_real

/-! ### Pulling, generic in the scalar ring: unital -/

attribute [cfc_pull]
  cfc_add cfc_sub cfc_neg cfc_mul cfc_pow cfc_smul cfc_star
  cfc_const cfc_const_one cfc_const_zero cfc_const_add cfc_add_const
  cfc_inv cfc_inv_id cfc_zpow cfc_ringInverse_id cfc_map_div
  cfc_map_polynomial cfc_polynomial
  cfc_neg_id cfc_pow_id cfc_smul_id cfc_star_id
  cfc_eq_cfcL cfc_apply_mkD cfc_eq_cfcL_mkD cfcHom_eq_cfc_extend_zero

-- preferred over `cfc_smul`, so that a scalar already living in the target ring produces
-- `r * f x` rather than `r • f x`
attribute [cfc_pull 1100] cfc_const_mul cfc_const_mul_id

/-! ### Pulling, generic in the scalar ring: non-unital -/

attribute [cfc_pull]
  cfcₙ_add cfcₙ_sub cfcₙ_neg cfcₙ_mul cfcₙ_smul cfcₙ_star cfcₙ_const_zero
  cfcₙ_neg_id cfcₙ_smul_id cfcₙ_star_id
  cfcₙ_eq_cfcₙL cfcₙ_apply_mkD cfcₙ_eq_cfcₙL_mkD cfcₙHom_eq_cfcₙ_extend_zero

attribute [cfc_pull 1100] cfcₙ_const_mul cfcₙ_const_mul_id

/-! ### Sums

`cfc_sum` and `cfcₙ_sum` collect a sum whose summands are applications of the calculus; `simp`
pulls the summands under the binder first. -/

attribute [cfc_pull] cfc_sum cfcₙ_sum

/-! ### Pulling, at a concrete scalar ring

The operations that are secretly an application of the calculus: positive and negative parts,
square roots, absolute values, powers, logarithms, exponentials, real and imaginary parts, the
spectral construction for a Hermitian matrix, and the `Unitization` bridges.

`cfc_tsub` and `cfcₙ_tsub` have lower priority than `cfc_sub`/`cfcₙ_sub` so that they still
apply over `ℝ≥0` but are not tried first since they generate side goals.

`CFC.real_exp_eq_normedSpace_exp` and `CFC.complex_exp_eq_normedSpace_exp` have higher priority so
that `Real.exp`/`Complex.exp` are produced in preference to `NormedSpace.exp`. -/

attribute [cfc_pull]
  CFC.posPart_def CFC.negPart_def
  CFC.sqrt_def CFC.sqrt_eq_cfc CFC.sqrt_eq_real_sqrt CFC.abs_def
  CFC.nnrpow_def CFC.rpow_def CFC.rpow_eq_cfc_real
  CFC.log_def CFC.exp_eq_normedSpace_exp
  cfc_re_id cfc_im_id cfcₙ_re_id cfcₙ_im_id
  Matrix.IsHermitian.cfc_eq
  Unitization.complex_cfcₙ_eq_cfc_inr Unitization.real_cfcₙ_eq_cfc_inr
  Unitization.nnreal_cfcₙ_eq_cfc_inr

attribute [cfc_pull 1100] CFC.real_exp_eq_normedSpace_exp CFC.complex_exp_eq_normedSpace_exp

attribute [cfc_pull 900] cfc_tsub cfcₙ_tsub

/- `CFC.sqrt_eq_cfc_complex_sqrt` and `CFC.sqrt_eq_cfcₙ_complex_sqrt` are not tagged, unlike
their real counterparts. This is because `Complex.sqrt` is continuous only away from the negative
reals, creating continuity side goals that are harder to discharge via `fun_prop`. -/

/-! ### Products

The components of a pair are pulled towards, as the components of `φ x` are: the holes of
`cfc_map_prod : cfc f (a, b) = (cfc f a, cfc f b)` are at `a` and `b`. Its hypotheses about the
predicate at the pair and at its components are not related by any tactic, so they come back as
`cfc_pull.predicate` goals. -/

attribute [cfc_pull] cfc_map_prod cfcₙ_map_prod

/-! ### Pulling through a homomorphism

Note that the element to pull towards lives in the *codomain*.

The morphism-specific lemmas should be used first, if possible, falling back to
the generic ones when they cannot be used. -/

attribute [cfc_pull] StarAlgHom.map_cfc NonUnitalStarAlgHom.map_cfcₙ

attribute [cfc_pull 900] StarAlgHomClass.map_cfc NonUnitalStarAlgHomClass.map_cfcₙ

/-! ### Composition -/

attribute [cfc_pull]
  cfc_comp' cfcₙ_comp'
  cfc_comp_pow cfc_comp_smul cfc_comp_star cfc_comp_neg cfc_comp_inv cfc_comp_zpow
  cfcₙ_comp_smul cfcₙ_comp_star cfcₙ_comp_neg
  cfc_comp_norm
  cfc_realPart cfc_imaginaryPart cfcₙ_realPart cfcₙ_imaginaryPart

attribute [cfc_pull 1100]
  cfc_comp_const_mul cfcₙ_comp_const_mul
  cfc_real_comp_norm cfcₙ_real_comp_norm
  cfc_complex_comp_norm cfcₙ_complex_comp_norm

/- The lemmas `cfc_comp_re`, `cfc_comp_im`, `cfcₙ_comp_re` and `cfcₙ_comp_im` are
deliberately *not* tagged. They change the scalar ring *and* the element and so are unsupported.

The lemmas `cfc_map_pi` and `cfcₙ_map_pi` are not tagged either: their holes, `cfc f (a i)`, are
under the binder of `fun i ↦ ..`, so the element `a i` to pull towards has a parameter, which the
targets of `cfc_pull` do not have. `cfc_apply_pi` and `cfcₙ_apply_pi` relate a family of
applications of the calculus to `cfcHom`, and are not pull lemmas at all. -/
