module

public import Mathlib.Topology.Algebra.ConstMulAction

@[expose] public section

/-- If `M` acts on `α` through `N` (i.e., `IsScalarTower M N α`), and the action of `N` on `α` is
continuous in the second variable, then so is the action of `M`. -/
@[to_additive /-- If `M` acts additively on `α` through `N` (i.e., `VAddAssocClass M N α`), and the
action of `N` on `α` is continuous in the second variable, then so is the action of `M`. -/]
theorem ContinuousConstSMul.restrictScalars (M N α : Type*) [SMul M N] [Monoid N] [MulAction N α]
    [SMul M α] [IsScalarTower M N α] [TopologicalSpace α] [ContinuousConstSMul N α] :
    ContinuousConstSMul M α where
  continuous_const_smul m := by
    simpa only [smul_one_smul] using continuous_const_smul (T := α) (m • (1 : N))
