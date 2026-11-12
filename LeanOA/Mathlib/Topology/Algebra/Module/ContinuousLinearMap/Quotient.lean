module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

@[expose] public section

namespace Submodule

variable {R R₂ : Type*} [Ring R] [Ring R₂] {σ : R →+* R₂} {M M₂ : Type*}
  [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]
  (S : Submodule R M)

@[simp]
theorem liftQL_comp_mkQL (f : M →SL[σ] M₂) (h : S ≤ f.ker) : (S.liftQL f h).comp S.mkQL = f :=
  rfl

end Submodule
