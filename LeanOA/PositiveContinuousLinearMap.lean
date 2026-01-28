import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Topology.Algebra.Module.LinearMap

/-- A `PositiveContinuousLinearMap` is a linear map which is both
positive and continuous. This comes equipped with the notation
`E₁ →P[R] E₂`. -/
structure PositiveContinuousLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [PartialOrder E₂] [TopologicalSpace E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₚ[R] E₂, E₁ →L[R] E₂

/-- Notation for a `PositiveContinuousLinearMap`. -/
notation:25 E " →P[" R:25 "] " F:0 => PositiveContinuousLinearMap R E F
