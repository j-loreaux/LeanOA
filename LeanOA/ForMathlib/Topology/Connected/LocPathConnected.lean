import LeanOA.ForMathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Algebra.OpenSubgroup

variable (G : Type*) [TopologicalSpace G]

/-- The path component of the identity in a locally path connected topological group,
as an open normal subgroup. -/
@[to_additive (attr := simps!)
"The path component of the identity in a locally path connected additive topological group,
as an open normal additive subgroup."]
def OpenNormalSubgroup.pathComponentOne [Group G]
    [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    OpenNormalSubgroup (G) where
  toSubgroup := .pathComponentOne G
  isOpen' := .pathComponent 1
  isNormal' := .pathComponentOne G

namespace OpenNormalSubgroup

@[to_additive]
instance [Group G] [IsTopologicalGroup G] [LocPathConnectedSpace G] :
    IsClosed (OpenNormalSubgroup.pathComponentOne G : Set G) :=
  .pathComponent 1

end OpenNormalSubgroup
