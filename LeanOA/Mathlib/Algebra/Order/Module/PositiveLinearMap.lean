module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Order.Group.Opposite
public import Mathlib.Algebra.Star.SelfAdjoint

@[expose] public section

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

section Id

variable {R E : Type*} [Semiring R] [AddCommMonoid E] [PartialOrder E] [Module R E]

variable (R E) in
/-- The identity as a positive linear map. -/
@[simps!] protected def id : E →ₚ[R] E where
  __ := LinearMap.id
  __ := OrderHom.id

@[simp] lemma toLinearMap_id : (PositiveLinearMap.id R E).toLinearMap = .id := rfl
@[simp] lemma toOrderHom_id : (PositiveLinearMap.id R E).toOrderHom = .id := rfl

end Id

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
