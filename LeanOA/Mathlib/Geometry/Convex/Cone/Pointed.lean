module

public import Mathlib.Geometry.Convex.Cone.Pointed

@[expose] public section

namespace PointedCone

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E]
  [Module R E]

lemma toConvexCone_hull (s : Set E) :
    (hull R s : ConvexCone R E) = ConvexCone.hull R (insert 0 s) := by
  refine le_antisymm (fun x hx ↦ ?_) <| ConvexCone.hull_min <|
    Set.insert_subset (Submodule.zero_mem _) subset_hull
  have hK : (ConvexCone.hull R (insert 0 s)).Pointed :=
    ConvexCone.subset_hull (Set.mem_insert 0 s)
  exact ConvexCone.hull R _ |>.toPointedCone hK |>.span_le.mpr
    ((Set.subset_insert 0 s).trans ConvexCone.subset_hull) hx

lemma toConvexCone_hull_of_zero_mem {s : Set E} (hs : 0 ∈ s) :
    (hull R s : ConvexCone R E) = ConvexCone.hull R s := by
  rw [toConvexCone_hull, Set.insert_eq_of_mem hs]

end PointedCone
