import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.Algebra.Order.Group.Opposite
import Mathlib.Algebra.Star.SelfAdjoint

/-- A class to encode that selfadjoint elements may be expressed as the
difference of nonnegative elements. This is satisfied by types with a
`NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint` instance.

This allows us to show that `PositiveLinearMap` is a `StarHomClass`. -/
class SelfAdjointDecompose (R : Type*) [AddGroup R] [Star R]
    [PartialOrder R] where
  /-- Every selfadjoint element is the difference of nonnegatives elements. -/
  exists_nonneg_sub_nonnpos {a : R} (ha : IsSelfAdjoint a) :
    ∃ (b c : R), 0 ≤ b ∧ 0 ≤ c ∧ a = b - c

lemma IsSelfAdjoint.exists_nonneg_sub_nonpos {R : Type*} [AddGroup R] [Star R]
    [PartialOrder R] [SelfAdjointDecompose R] {a : R} (ha : IsSelfAdjoint a) :
    ∃ (b c : R), 0 ≤ b ∧ 0 ≤ c ∧ a = b - c :=
  SelfAdjointDecompose.exists_nonneg_sub_nonnpos ha

namespace PositiveLinearMap

initialize_simps_projections PositiveLinearMap (toFun → apply)

section MulOpposite
-- this section is probably unnecessary
open MulOpposite

variable {R E : Type*} [Semiring R] [AddCommMonoid E] [PartialOrder E] [Module R E]

/-- `MulOpposite.op` as a positive linear map -/
@[simps!]
protected def op : E →ₚ[R] Eᵐᵒᵖ where
  toLinearMap := (opLinearEquiv R).toLinearMap
  monotone' _ _ h := h

/-- `MulOpposite.unop` as a positive linear map -/
protected def unop : Eᵐᵒᵖ →ₚ[R] E where
  toLinearMap := (opLinearEquiv R).symm.toLinearMap
  monotone' _ _ h := h

@[simp]
lemma unop_apply (x : Eᵐᵒᵖ) : PositiveLinearMap.unop (R := R) x = unop x := rfl

end MulOpposite

section Comp
-- this section is probably unnecessary (for now)

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]

/-- The composition of positive linear maps is again a positive linear map. -/
@[simps!]
def comp (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂) : E₁ →ₚ[R] E₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'

end Comp

end PositiveLinearMap
