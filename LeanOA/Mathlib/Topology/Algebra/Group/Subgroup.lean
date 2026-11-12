module

public import Mathlib.Topology.Algebra.Group.Subgroup

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A subgroup of a topological group is dense if and only if its topological closure is the
entire group. -/
@[to_additive /-- An additive subgroup of a topological group is dense if and only if its
topological closure is the entire group. -/]
theorem dense_iff_topologicalClosure_eq_top {s : Subgroup G} :
    Dense (s : Set G) ↔ s.topologicalClosure = ⊤ := by
  rw [← SetLike.coe_set_eq, dense_iff_closure_eq]
  simp

end Subgroup
