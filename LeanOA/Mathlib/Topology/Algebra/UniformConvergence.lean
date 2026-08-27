module

public import Mathlib.Topology.Algebra.UniformConvergence

@[expose] public section

open scoped UniformConvergence

namespace UniformOnFun

variable {α β R : Type*} (𝔖 : Set (Set α))

/-- `UniformOnFun.toFun` as a linear equivalence. -/
@[simps!]
def toFunAddEquiv [AddCommMonoid β] : (α →ᵤ[𝔖] β) ≃+ (α → β) where
  toEquiv := toFun 𝔖
  map_add' _ _ := rfl

/-- `UniformOnFun.toFun` as an additive group equivalence. -/
@[simps!]
def toFunLinearEquiv [Semiring R] [AddCommMonoid β] [Module R β] :
    (α →ᵤ[𝔖] β) ≃ₗ[R] (α → β) where
  toAddEquiv := toFunAddEquiv 𝔖
  map_smul' _ _ := rfl

end UniformOnFun
