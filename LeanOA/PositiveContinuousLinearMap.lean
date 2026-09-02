module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

@[expose] public section

namespace PositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommGroup E₁] [PartialOrder E₁]
    [NonUnitalRing E₂] [PartialOrder E₂]
    [Star E₁] [StarRing E₂] [StarOrderedRing E₂]
    [Module R E₁] [Module R E₂] [SelfAdjointDecompose E₁]

lemma map_isSelfAdjoint (f : E₁ →ₚ[R] E₂) {a : E₁} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (f a) := by
  obtain ⟨b, c, hb, hc, rfl⟩ := ha.exists_nonneg_sub_nonneg
  cfc_tac

end PositiveLinearMap
