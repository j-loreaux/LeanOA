import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-! # missing lemmas about topological star algebras -/

open Topology

-- missing lemma
lemma NonUnitalStarAlgHom.range_eq_map_top {F R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarRing A] [StarModule R A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B] (φ : F) :
    NonUnitalStarAlgHom.range φ = NonUnitalStarSubalgebra.map φ ⊤ := by
  aesop

namespace NonUnitalSubalgebra

variable {F R A B : Type*} [CommSemiring R]
    [TopologicalSpace A] [NonUnitalSemiring A] [Module R A] [TopologicalSemiring A] [ContinuousConstSMul R A]
    [TopologicalSpace B] [NonUnitalSemiring B] [Module R B] [TopologicalSemiring B] [ContinuousConstSMul R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (s : NonUnitalSubalgebra R A) (φ : F)

-- should be generalized to `[ContinuousMapClass F A B]` instead of `Continuous φ` once we have a type that will satisfy both
lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

lemma topologicalClosure_map_le (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

lemma topologicalClosure_map (hφ : IsClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

end NonUnitalSubalgebra

namespace NonUnitalStarSubalgebra

variable {F R A B : Type*} [CommSemiring R]
    [TopologicalSpace A] [Star A] [NonUnitalSemiring A] [Module R A] [TopologicalSemiring A] [ContinuousConstSMul R A] [ContinuousStar A]
    [TopologicalSpace B] [Star B] [NonUnitalSemiring B] [Module R B] [TopologicalSemiring B] [ContinuousConstSMul R B] [ContinuousStar B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B] (s : NonUnitalStarSubalgebra R A) (φ : F)

-- should be generalized to `[ContinuousMapClass F A B]` instead of `Continuous φ` once we have a type that will satisfy both
lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

lemma topologicalClosure_map_le (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _

lemma topologicalClosure_map (hφ : IsClosedEmbedding φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq _

end NonUnitalStarSubalgebra
