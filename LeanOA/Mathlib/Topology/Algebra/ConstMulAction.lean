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

open Set Topology

namespace MulAction.IsPretransitive

variable (G : Type*) {α : Type*} [Group G] [TopologicalSpace α] [MulAction G α]
  [ContinuousConstSMul G α]

/-- If `G` acts pretransitively and continuously on `α`, then `α` has the indiscrete topology if
and only if some (equivalently, every) point is dense. -/
@[to_additive /-- If `G` acts additively, pretransitively and continuously on `α`, then `α` has the
indiscrete topology if and only if some (equivalently, every) point is dense. -/]
protected lemma indiscreteTopology_iff (x : α) [IsPretransitive G α] :
    IndiscreteTopology α ↔ Dense {x} := by
  refine ⟨fun _ ↦ dense_indiscrete (singleton_nonempty x), fun h ↦ ?_⟩
  have key (y z : α) : y ⤳ z := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    simpa using (specializes_iff_mem_closure.mpr (h (g⁻¹ • z))).map (continuous_const_smul g)
  exact .of_forall_inseparable fun y z ↦ (key y z).antisymm (key z y)

@[to_additive]
alias ⟨_, indiscreteTopology⟩ := IsPretransitive.indiscreteTopology_iff

/-- If `G` acts pretransitively and continuously on `α`, then `α` has a nontrivial topology if and
only if some (equivalently, every) point is not dense. -/
@[to_additive /-- If `G` acts additively, pretransitively and continuously on `α`, then `α` has a
nontrivial topology if and only if some (equivalently, every) point is not dense. -/]
protected lemma nontrivialTopology_iff (x : α) [IsPretransitive G α] :
    NontrivialTopology α ↔ ¬Dense {x} := by
  rw [← TopologicalSpace.not_indiscrete_iff, IsPretransitive.indiscreteTopology_iff G x]

@[to_additive]
alias ⟨_, nontrivialTopology⟩ := IsPretransitive.nontrivialTopology_iff

@[to_additive]
lemma not_dense_singleton [NontrivialTopology α] (x : α) [IsPretransitive G α] : ¬Dense {x} :=
  (IsPretransitive.nontrivialTopology_iff G x).mp ‹_›

end MulAction.IsPretransitive
