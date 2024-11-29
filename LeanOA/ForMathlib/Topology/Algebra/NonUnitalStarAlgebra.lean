/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-! # Non-unital topological star (sub)algebras

[PR #18615](https://github.com/leanprover-community/mathlib4/pull/18615/files)

Adds elemental non-unital star subalgebras and basic properties.
-/

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [TopologicalSpace A] [TopologicalSemiring A] [ContinuousConstSMul R A] [ContinuousStar A]

/-- The topological closure of the non-unital star subalgebra generated by a single element. -/
def elemental (x : A) : NonUnitalStarSubalgebra R A :=
  adjoin R {x} |>.topologicalClosure

namespace elemental

@[aesop safe apply (rule_sets := [SetLike])]
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

@[aesop safe apply (rule_sets := [SetLike])]
theorem star_self_mem (x : A) : star x ∈ elemental R x :=
  le_topologicalClosure _ <| star_self_mem_adjoin_singleton R x

variable {R} in
theorem le_of_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
    (hx : x ∈ s) : elemental R x ≤ s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

variable {R} in
theorem le_iff_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩

instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

instance [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommSemiring (elemental R x) :=
  nonUnitalCommSemiringTopologicalClosure _ <| by
    letI : NonUnitalCommSemiring (adjoin R {x}) := by
      refine NonUnitalStarAlgebra.adjoinNonUnitalCommSemiringOfComm R ?_ ?_
      all_goals
        intro y hy z hz
        rw [Set.mem_singleton_iff] at hy hz
        rw [hy, hz]
      exact (star_comm_self' x).symm
    exact fun _ _ => mul_comm _ _

instance {R A : Type*} [CommRing R] [StarRing R] [NonUnitalRing A] [StarRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    [TopologicalSpace A] [TopologicalRing A] [ContinuousConstSMul R A] [ContinuousStar A]
    [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A] [StarRing A]
    [TopologicalSemiring A] [ContinuousStar A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

end elemental

end NonUnitalStarAlgebra