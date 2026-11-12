module

public import Mathlib.Topology.Algebra.Module.Basic
public import LeanOA.Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] {S : Submodule R M}

protected theorem indiscreteTopology_iff :
    IndiscreteTopology (M ⧸ S) ↔ S.topologicalClosure = ⊤ := by
  rw [← dense_iff_topologicalClosure_eq_top]
  exact (QuotientAddGroup.indiscreteTopology_iff (N := S.toAddSubgroup)).trans
    AddSubgroup.dense_iff_topologicalClosure_eq_top.symm

alias ⟨_, indiscreteTopology⟩ := Submodule.Quotient.indiscreteTopology_iff

variable (S) in
theorem topologicalClosure_eq_top [IndiscreteTopology (M ⧸ S)] : S.topologicalClosure = ⊤ :=
  Submodule.Quotient.indiscreteTopology_iff.mp ‹_›

protected theorem nontrivialTopology_iff :
    NontrivialTopology (M ⧸ S) ↔ S.topologicalClosure ≠ ⊤ := by
  rw [← TopologicalSpace.not_indiscrete_iff, Submodule.Quotient.indiscreteTopology_iff]

alias ⟨_, nontrivialTopology⟩ := Submodule.Quotient.nontrivialTopology_iff

variable (S) in
theorem topologicalClosure_ne_top [NontrivialTopology (M ⧸ S)] : S.topologicalClosure ≠ ⊤ :=
  Submodule.Quotient.nontrivialTopology_iff.mp ‹_›

end Submodule.Quotient
