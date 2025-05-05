import Mathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected


variable {G : Type*} [TopologicalSpace G]

/-- Pointwise inversion of paths in a topological group. -/
@[to_additive (attr := simps) "Pointwise negation of paths in a topological group."]
def Path.inv {x y : G} [Inv G] [ContinuousInv G] (γ : Path x y) :
    Path (x⁻¹) (y⁻¹) where
  toFun := γ⁻¹
  continuous_toFun := map_continuous γ |>.inv
  source' := congr($(γ.source)⁻¹)
  target' := congr($(γ.target)⁻¹)
