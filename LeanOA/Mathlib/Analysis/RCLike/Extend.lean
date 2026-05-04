/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Analysis.Normed.Module.WeakDual

@[expose] public section

/-!
# Extending an `ℝ`-linear functional to a `𝕜`-linear functional

In this file we provide a way to extend a (optionally, continuous) `ℝ`-linear map to a (continuous)
`𝕜`-linear map in a way that bounds the norm by the norm of the original map, when `𝕜` is either
`ℝ` (the extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `RCLike 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `im (fc x) = -re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

In `Mathlib/Analysis/Normed/Module/RCLike/Extend.lean` we show that this extension is isometric.
This is separate to avoid importing material about the operator norm into files about more
elementary properties, like locally convex spaces.

## Main definitions

* `LinearMap.extendRCLike`
* `ContinuousLinearMap.extendRCLike`

-/

@[expose] public section

open StrongDual WeakDual

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

lemma StrongDual.symm_toWeakDual :
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).symm = WeakDual.toStrongDual :=
  rfl

lemma WeakDual.symm_toStrongDual :
    (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).symm = StrongDual.toWeakDual :=
  rfl

@[simp]
lemma toStrongDual_toWeakDual_apply (f : StrongDual 𝕜 E) :
    toStrongDual (toWeakDual f) = f :=
  rfl

@[simp]
lemma toWeakDual_toStrongDual_apply (f : WeakDual 𝕜 E) :
    toWeakDual (toStrongDual f) = f :=
  rfl

open RCLike

open ComplexConjugate

/-- A map in `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` over `𝕜` (with `RCLike 𝕜`) is
continuous if the real parts of all the evaluation maps `a ↦ B (g a) y` are
continuous for each `y : F`. -/
theorem WeakBilin.continuous_of_continuous_eval_re
    {α 𝕜 E F : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a ↦ re ((B (g a)) y)) :
    Continuous g := by
  refine continuous_of_continuous_eval _ fun x ↦ ?_
  have : Continuous fun a ↦ (re (B (g a) x) : 𝕜) - re (B (g a) ((I : 𝕜) • x)) * I := by
    fun_prop
  convert this
  simp

namespace WeakDual

/-- A map into `WeakDual 𝕜 E` (with `RCLike 𝕜`) is continuous if the real parts of all the
evaluation maps `a ↦ g a x` are continuous for each `x : E`. -/
lemma continuous_of_continuous_eval_re
    {α 𝕜 E : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
    [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ x, Continuous fun a ↦ re (g a x)) :
    Continuous g :=
  WeakBilin.continuous_of_continuous_eval_re _ h

variable {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [ContinuousConstSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The extension `StrongDual.extendRCLike` as a continuous linear equivalence between
the weak duals. -/
noncomputable def extendRCLikeL : WeakDual ℝ F ≃L[ℝ] WeakDual 𝕜 F where
  toLinearEquiv := toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars ℝ
  continuous_toFun := continuous_of_continuous_eval_re fun x ↦ by
    simpa [StrongDual.extendRCLikeₗ_apply] using eval_continuous (𝕜 := ℝ) x
  continuous_invFun :=
    continuous_of_continuous_eval fun x ↦ RCLike.continuous_re.comp (eval_continuous x)

end WeakDual
