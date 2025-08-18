import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.StarSubalgebra

/-! # missing lemmas about topological star algebras -/

open Topology


namespace Set

-- Mathlib.Topology.Algebra.Group.Basic
lemma isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, setOf_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
  refine isClosed_imp (by simp) <| isClosed_eq ?_ ?_
  all_goals fun_prop

end Set

-- missing lemma
lemma NonUnitalStarAlgHom.range_eq_map_top {F R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarRing A] [StarModule R A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B] (φ : F) :
    NonUnitalStarAlgHom.range φ = NonUnitalStarSubalgebra.map φ ⊤ := by
  aesop

namespace StarAlgebra

open StarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [Algebra R A]
  [StarRing A] [StarModule R A] [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousStar A]
  [T2Space A]

lemma topologicalClosure_adjoin_le_centralizer_centralizer (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

lemma elemental.le_centralizer_centralizer (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer R {x}

end StarAlgebra
namespace NonUnitalSubalgebra

variable {F R A B : Type*} [CommSemiring R]
    [TopologicalSpace A] [NonUnitalSemiring A] [Module R A] [IsTopologicalSemiring A] [ContinuousConstSMul R A]
    [TopologicalSpace B] [NonUnitalSemiring B] [Module R B] [IsTopologicalSemiring B] [ContinuousConstSMul R B]
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
    [TopologicalSpace A] [Star A] [NonUnitalSemiring A] [Module R A] [IsTopologicalSemiring A] [ContinuousConstSMul R A] [ContinuousStar A]
    [TopologicalSpace B] [Star B] [NonUnitalSemiring B] [Module R B] [IsTopologicalSemiring B] [ContinuousConstSMul R B] [ContinuousStar B]
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

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [StarRing A] [StarModule R A] [TopologicalSpace A] [IsTopologicalSemiring A] [ContinuousStar A]
  [T2Space A] [ContinuousConstSMul R A]

lemma topologicalClosure_adjoin_le_centralizer_centralizer (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

lemma elemental.le_centralizer_centralizer (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer R {x}

end NonUnitalStarAlgebra
