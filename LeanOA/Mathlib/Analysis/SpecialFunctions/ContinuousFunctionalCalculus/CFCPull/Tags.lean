/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.CFCPull.Lemmas
public import LeanOA.Mathlib.Tactic.CFCPull.Attr

/-!
# The `@[cfc_pull]` lemma set

This file tags Mathlib's continuous functional calculus lemmas with `@[cfc_pull]`, building the
database the `cfc_pull` tactic searches. Nothing else happens here: every lemma named below is
proved elsewhere, and the tags are collected in one place rather than written at the declaration
sites so that the tactic and everything supporting it can be read, reviewed and landed as a
self-contained unit.

The categories a lemma can fall into (`Id`, `Pull`, `Scalar`, `Unital`, `Compose`) are described
in `LeanOA/Mathlib/Tactic/CFCPull/Spec.md` §4; the attribute works out which one applies from
the shape of the lemma's statement. §9 of the same document walks through the set below and says
why each group is there. The sections here follow that walkthrough.

Where a lemma is *deliberately* absent, the reason is recorded in a comment next to the group it
would have joined.
-/

public section

open scoped NNReal

/-! ### Identity

The lemmas that say the calculus applied to the identity function is the element itself. -/

attribute [cfc_pull] cfc_id' cfcₙ_id'

/-! ### Unitality

The bridge from the non-unital calculus to the unital one, used whenever a `cfcₙ` shows up in a
goal that asks for a `cfc`. -/

attribute [cfc_pull] cfcₙ_eq_cfc

/-! ### Scalars

Widening (`ℝ≥0 → ℝ → ℂ`) and narrowing (`ℂ → ℝ → ℝ≥0`) conversions. The four narrowing lemmas
carry a hypothesis the tactic cannot read off the syntax, which comes back as a
`cfc_pull.side` goal; they are tagged all the same, so that any two of the three rings are
reachable from one another. -/

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

`cfc_sum` and `cfcₙ_sum` cannot pull *through* a sum, but they collect one whose summands are
already applications of the calculus, which is the second half of the staged idiom of
`Spec.md` §11. Their algebraic side has a hole under a binder, which the attribute warns about
by default. -/

set_option cfcPull.warnBoundHoles false in
attribute [cfc_pull] cfc_sum cfcₙ_sum

/-! ### Pulling, at a concrete scalar ring

The operations that are secretly an application of the calculus: positive and negative parts,
square roots, absolute values, powers, logarithms, exponentials, real and imaginary parts, the
spectral construction for a Hermitian matrix, and the `Unitization` bridges.

`cfc_tsub` and `cfcₙ_tsub` sit at priority 900, below the generic `cfc_sub`/`cfcₙ_sub` that win
wherever the scalars form a ring; over `ℝ≥0` those are rejected by instance synthesis and the
truncated versions take over, at the cost of a `cfc_pull.side` goal.

`CFC.real_exp_eq_normedSpace_exp` and `CFC.complex_exp_eq_normedSpace_exp` sit at 1100 so that
`Real.exp`/`Complex.exp` are produced in preference to `NormedSpace.exp`. -/

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

/- The generic `Unitization.cfcₙ_eq_cfc_inr` is *not* tagged: its `hp` hypothesis relating the
two predicates is not something the tactic can discharge.

`CFC.sqrt_eq_cfc_complex_sqrt` and `CFC.sqrt_eq_cfcₙ_complex_sqrt` are not tagged either, for a
different reason; see the module docstring of
`LeanOA/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/CFCPull/ComplexSqrt.lean`. -/

/-! ### Pulling through a homomorphism

Note that the element to pull towards lives in the *codomain*. -/

attribute [cfc_pull] StarAlgHom.map_cfc NonUnitalStarAlgHom.map_cfcₙ

/- The `...Class` counterparts `StarAlgHomClass.map_cfc` and `NonUnitalStarAlgHomClass.map_cfcₙ`
are **not** tagged: their auxiliary scalar ring `S` occurs only in the instance arguments and so
is undetermined at application time. See `Spec.md` §11. -/

/-! ### Composition -/

attribute [cfc_pull]
  cfc_comp' cfcₙ_comp'
  cfc_comp_pow cfc_comp_smul cfc_comp_star cfc_comp_neg cfc_comp_inv cfc_comp_zpow
  cfcₙ_comp_smul cfcₙ_comp_star cfcₙ_comp_neg
  cfc_comp_norm
  cfc_realPart cfc_imaginaryPart cfcₙ_realPart cfcₙ_imaginaryPart

attribute [cfc_pull 1100] cfc_comp_const_mul cfcₙ_comp_const_mul

/- The `ℝ`-valued companions `cfc_comp_re`, `cfc_comp_im`, `cfcₙ_comp_re` and `cfcₙ_comp_im` are
deliberately *not* tagged. They change the scalar ring (`ℝ` on the side with the structured
element `ℜ a`, `ℂ` on the side with the element `a`) *and* the element, and the `@[cfc_pull]`
attribute classifies any lemma whose two sides disagree about the scalar ring as a `Scalar`
conversion, without looking at the elements. Tagging them would therefore add a bogus `ℂ → ℝ`
edge to the conversion graph, along which `cfc_pull` would happily "convert" a result at `a`
into one at `ℜ a`. Supporting them needs a `Compose` category that is allowed to change the
ring; see `Spec.md` §11.

`cfc_apply_pi`, `cfc_map_pi`, `cfc_map_prod` and `cfcₙ_map_prod` are not tagged either. For the
last two there are two independent reasons: the auxiliary scalar ring `S` occurs only in the
hypotheses, so `cfc_pull` cannot determine it when it applies the lemma; and even with `S`
pinned down the two components `cfc f a` and `cfc f b` are not *holes* — a hole must be an
application of the calculus at the element and in the algebra being pulled towards, here
`(a, b)` in `A × B` — so the lemma could only collect a pair that is already of the form
`(cfc f a, cfc f b)`, never build one component by component. See `Spec.md` §11. -/
