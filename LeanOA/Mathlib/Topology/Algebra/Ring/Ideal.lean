module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Topology.Algebra.Ring.Ideal
public import LeanOA.Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace Ideal.Quotient

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R] {I : Ideal R}

protected theorem indiscreteTopology_iff : IndiscreteTopology (R ⧸ I) ↔ I.closure = ⊤ := by
  rw [← SetLike.coe_set_eq, coe_closure, Submodule.top_coe, ← dense_iff_closure_eq]
  exact (QuotientAddGroup.indiscreteTopology_iff (N := I.toAddSubgroup)).trans
    AddSubgroup.dense_iff_topologicalClosure_eq_top.symm

alias ⟨_, indiscreteTopology⟩ := Ideal.Quotient.indiscreteTopology_iff

variable (I) in
theorem closure_eq_top [IndiscreteTopology (R ⧸ I)] : I.closure = ⊤ :=
  Ideal.Quotient.indiscreteTopology_iff.mp ‹_›

protected theorem nontrivialTopology_iff : NontrivialTopology (R ⧸ I) ↔ I.closure ≠ ⊤ := by
  rw [← TopologicalSpace.not_indiscrete_iff, Ideal.Quotient.indiscreteTopology_iff]

alias ⟨_, nontrivialTopology⟩ := Ideal.Quotient.nontrivialTopology_iff

variable (I) in
theorem closure_ne_top [NontrivialTopology (R ⧸ I)] : I.closure ≠ ⊤ :=
  Ideal.Quotient.nontrivialTopology_iff.mp ‹_›

end Ideal.Quotient
