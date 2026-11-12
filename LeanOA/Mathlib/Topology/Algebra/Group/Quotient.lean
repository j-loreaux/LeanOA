module

public import Mathlib.Topology.Algebra.Group.Quotient
public import LeanOA.Mathlib.Topology.Algebra.ConstMulAction
public import LeanOA.Mathlib.Topology.Algebra.Group.Subgroup

@[expose] public section

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}

/-- A quotient group has the indiscrete topology if and only if the topological closure of the
subgroup is the entire group. -/
@[to_additive /-- The quotient by an additive subgroup has the indiscrete topology if and only if
the topological closure of the subgroup is the entire group. -/]
protected theorem indiscreteTopology_iff :
    IndiscreteTopology (G ⧸ N) ↔ N.topologicalClosure = ⊤ := by
  rw [← Subgroup.dense_iff_topologicalClosure_eq_top,
    MulAction.IsPretransitive.indiscreteTopology_iff G (mk 1 : G ⧸ N), ← dense_preimage_mk,
    preimage_mk_one]

@[to_additive]
alias ⟨_, indiscreteTopology⟩ := QuotientGroup.indiscreteTopology_iff

variable (N) in
@[to_additive]
theorem topologicalClosure_eq_top [IndiscreteTopology (G ⧸ N)] : N.topologicalClosure = ⊤ :=
  QuotientGroup.indiscreteTopology_iff.mp ‹_›

/-- A quotient group has a nontrivial topology if and only if the topological closure of the
subgroup is not the entire group. -/
@[to_additive /-- The quotient by an additive subgroup has a nontrivial topology if and only if
the topological closure of the subgroup is not the entire group. -/]
protected theorem nontrivialTopology_iff :
    NontrivialTopology (G ⧸ N) ↔ N.topologicalClosure ≠ ⊤ := by
  rw [← TopologicalSpace.not_indiscrete_iff, QuotientGroup.indiscreteTopology_iff]

@[to_additive]
alias ⟨_, nontrivialTopology⟩ := QuotientGroup.nontrivialTopology_iff

variable (N) in
@[to_additive]
theorem topologicalClosure_ne_top [NontrivialTopology (G ⧸ N)] : N.topologicalClosure ≠ ⊤ :=
  QuotientGroup.nontrivialTopology_iff.mp ‹_›

end QuotientGroup
