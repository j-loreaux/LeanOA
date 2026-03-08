import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.CStarAlgebra.Classes

section IsMulCommutative

variable {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]

lemma isMulCommutative_iff : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

alias ⟨IsMulCommutative.mul_comm, IsMulCommutative.of_forall_comm⟩ := isMulCommutative_iff

lemma isMulCommutative_iff_of_setLike {s : S} :
    IsMulCommutative s ↔ ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
  simp [isMulCommutative_iff]

alias ⟨IsMulCommutative.setLike_mul_comm, IsMulCommutative.of_setLike_mul_comm⟩ :=
  isMulCommutative_iff_of_setLike

instance Algebra.instIsMulCommutativeAdjoin {S R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [SetLike S A] [MulMemClass S A] (s : S) [hs : IsMulCommutative s] :
    IsMulCommutative (adjoin R (s : Set A)) :=
  let := adjoinCommSemiringOfComm R hs.setLike_mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalAlgebra.instIsMulCommutativeAdjoin {S R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [SetLike S A] [MulMemClass S A] (s : S) [hs : IsMulCommutative s] :
    IsMulCommutative (adjoin R (s : Set A)) :=
  let := adjoinNonUnitalCommSemiringOfComm R hs.setLike_mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalStarAlgebra.instIsMulCommutativeAdjoin {S R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarRing A] [StarRing R] [StarModule R A]
    [SetLike S A] [MulMemClass S A] [StarMemClass S A] (s : S) [hs : IsMulCommutative s] :
    IsMulCommutative (adjoin R (s : Set A)) :=
  let := adjoinNonUnitalCommSemiringOfComm R hs.setLike_mul_comm
    (fun a ha b hb ↦ hs.setLike_mul_comm a ha (star b) (star_mem hb))
  ⟨⟨mul_comm⟩⟩

instance StarAlgebra.instIsMulCommutativeAdjoin {S R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [StarRing A] [StarRing R] [StarModule R A]
    [SetLike S A] [MulMemClass S A] [StarMemClass S A] (s : S) [hs : IsMulCommutative s] :
    IsMulCommutative (adjoin R (s : Set A)) :=
  let := adjoinCommSemiringOfComm R hs.setLike_mul_comm
    (fun a ha b hb ↦ hs.setLike_mul_comm a ha (star b) (star_mem hb))
  ⟨⟨mul_comm⟩⟩

instance Subalgebra.instIsMulCommutativeToNonUnitalSubalgebra {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] (S : Subalgebra R A) [hS : IsMulCommutative S] :
    IsMulCommutative S.toNonUnitalSubalgebra :=
  hS

instance StarSubalgebra.instIsMulCommutativeToNonUnitalStarSubalgebra {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [StarRing A] [StarRing R] [StarModule R A]
    (S : StarSubalgebra R A) [hS : IsMulCommutative S] :
    IsMulCommutative S.toNonUnitalStarSubalgebra :=
  hS

instance Subsemigroup.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [Semigroup A] [ContinuousMul A] [T2Space A]
    (s : Subsemigroup A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commSemigroupTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance Submonoid.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [Monoid A] [ContinuousMul A] [T2Space A]
    (s : Submonoid A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commMonoidTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalSubsemiring.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [NonUnitalSemiring A] [IsTopologicalSemiring A] [T2Space A]
    (s : NonUnitalSubsemiring A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.nonUnitalCommSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance Subsemiring.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [T2Space A]
    (s : Subsemiring A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalSubring.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [NonUnitalRing A] [IsTopologicalRing A] [T2Space A]
    (s : NonUnitalSubring A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.nonUnitalCommRingTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance Subring.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [Ring A] [IsTopologicalRing A] [T2Space A]
    (s : Subring A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commRingTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalStarSubalgebra.instIsMulCommutativeTopologicalClosure {R A : Type*}
    [CommSemiring R] [TopologicalSpace A] [Star A] [NonUnitalSemiring A] [Module R A]
    [IsTopologicalSemiring A] [ContinuousStar A] [ContinuousConstSMul R A] [T2Space A]
    (s : NonUnitalStarSubalgebra R A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.nonUnitalCommSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance NonUnitalSubalgebra.instIsMulCommutativeTopologicalClosure {R A : Type*}
    [CommSemiring R] [TopologicalSpace A] [NonUnitalSemiring A] [Module R A]
    [IsTopologicalSemiring A] [ContinuousConstSMul R A] [T2Space A]
    (s : NonUnitalSubalgebra R A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.nonUnitalCommSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance Subalgebra.instIsMulCommutativeTopologicalClosure {R A : Type*}
    [CommSemiring R] [TopologicalSpace A] [Semiring A] [Algebra R A]
    [IsTopologicalSemiring A] [T2Space A]
    (s : Subalgebra R A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

instance StarSubalgebra.instIsMulCommutativeTopologicalClosure {R A : Type*}
    [CommSemiring R] [StarRing R] [TopologicalSpace A] [Semiring A] [StarRing A] [Algebra R A]
    [StarModule R A] [IsTopologicalSemiring A] [ContinuousStar A]
    [T2Space A] (s : StarSubalgebra R A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commSemiringTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

-- we should have non-star and also unital versions of this, as well as for other subobjects.
theorem NonUnitalStarSubalgebra.isMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] {ι : Type*} [StarRing R] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) := by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, NonUnitalStarSubalgebra.coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact (hS k).setLike_mul_comm a (hik ha) b (hjk hb)

namespace IsMulCommutative

variable {R : Type*}

@[to_additive]
instance (priority := 100) [Mul R] [Subsingleton R] : IsMulCommutative R where
  is_comm := ⟨fun _ _ ↦ Subsingleton.elim ..⟩

-- I think these instances should be scoped.

/-- A multiplicative type with commutative multiplication is a commutative multiplicative magma. -/
scoped instance (priority := 50) [Mul R] [IsMulCommutative R] : CommMagma R where
  mul_comm := IsMulCommutative.mul_comm inferInstance

/-- A nonunital semiring with commutative multiplication is a commutative non-unital semiring. -/
scoped instance (priority := 50) [NonUnitalSemiring R] [IsMulCommutative R] :
    NonUnitalCommSemiring R where

/-- A semiring with commutative multiplication is a commutative semiring. -/
scoped instance (priority := 50) [Semiring R] [IsMulCommutative R] : CommSemiring R where

/-- A nonunital ring with commutative multiplication is a commutative nonunital ring. -/
scoped instance (priority := 50) [NonUnitalRing R] [IsMulCommutative R] : NonUnitalCommRing R where

/-- A ring with commutative multiplication is a commutative ring. -/
scoped instance (priority := 50) [Ring R] [IsMulCommutative R] : CommRing R where

/-- A nonunital seminiormed ring with commutative multiplication is a commutative nonunital
seminormed ring. -/
scoped instance (priority := 50) [NonUnitalSeminormedRing R] [IsMulCommutative R] :
    NonUnitalSeminormedCommRing R where

/-- A seminormed ring with commutative multiplication is a commutative seminormed ring. -/
scoped instance (priority := 50) [SeminormedRing R] [IsMulCommutative R] :
    SeminormedCommRing R where

/-- A nonunital normed ring with commutative multiplication is a commutative nonunital normed
ring. -/
scoped instance (priority := 50) [NonUnitalNormedRing R] [IsMulCommutative R] :
    NonUnitalNormedCommRing R where

/-- A normed ring with commutative multiplication is a commutative normed ring. -/
scoped instance (priority := 50) [NormedRing R] [IsMulCommutative R] : NormedCommRing R where

/-- A nonunital C⋆-algebra with commutative multiplication is a commutative nonunital C⋆-algebra. -/
scoped instance (priority := 50) [NonUnitalCStarAlgebra R] [IsMulCommutative R] :
    NonUnitalCommCStarAlgebra R where

/-- A C⋆-algebra with commutative multiplication is a commutative C⋆-algebra. -/
scoped instance (priority := 50) [CStarAlgebra R] [IsMulCommutative R] : CommCStarAlgebra R where

end IsMulCommutative

end IsMulCommutative

section NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

/-- A *maximal abelian star subalgebra* (often abbreviated to *masa* or *MASA*) is a commutative
non-unital star subalgebra which is maximal with respect to these properties.

In a unital algebra, a masa is in fact always unital (since adjoining `1` does not affect
commutativity), see `NonUnitalStarSubalgebra.IsMasa.one_mem`. -/
class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop extends
    IsMulCommutative B where
  maximal (C : NonUnitalStarSubalgebra R A) [hC : IsMulCommutative C] (hBC : B ≤ C) : C ≤ B

/-- Every commutative non-unital star subalgebra is contained in a masa. -/
theorem NonUnitalStarSubalgebra.exists_le_isMasa (B : NonUnitalStarSubalgebra R A)
    [hB : IsMulCommutative B] : ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa := by
  obtain ⟨C, hC⟩ := by
    apply zorn_le (α := {C : NonUnitalStarSubalgebra R A // IsMulCommutative C ∧ B ≤ C})
    intro chain hchain
    obtain (rfl | h) := chain.eq_empty_or_nonempty
    · exact ⟨⟨B, hB, le_rfl⟩, by simp⟩
    · have := h.to_subtype
      have hdir : Directed (· ≤ ·) fun S : chain ↦ S.val.val :=
        hchain.directedOn.directed_val.mono_comp _ (by simp)
      have h_comm : ∀ S : chain, IsMulCommutative S.val.val := fun S ↦ S.val.prop.1
      let bound : NonUnitalStarSubalgebra R A := ⨆ S : chain, S
      refine ⟨⟨bound, ?_, ?_⟩, ?_⟩
      · exact NonUnitalStarSubalgebra.isMulCommutative_iSup hdir
      · exact Classical.arbitrary chain |>.val.prop.2 |>.trans <|
          le_iSup (fun S : chain ↦ S.val.val) _
      · intro S hS
        lift S to chain using hS
        exact le_iSup (fun S : chain ↦ S.val.val) _
  refine ⟨C, C.prop.2, ?_⟩
  have hC' := C.prop.1
  exact ⟨fun S hS hCS ↦ @hC ⟨S, hS, C.prop.2.trans hCS⟩ hCS⟩

end NonUnitalStarSubalgebra
section TopologicalAlgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
variable [ContinuousConstSMul R A] [ContinuousStar A] [T2Space A]

/-- A masa in a topological star algebra is closed. -/
instance NonUnitalStarSubalgebra.IsMasa.isClosed (B : NonUnitalStarSubalgebra R A) [hB : B.IsMasa] :
    IsClosed (B : Set A) :=
  closure_subset_iff_isClosed.mp <| hB.maximal _ B.le_topologicalClosure

end TopologicalAlgebra

section Unital

variable {R A : Type*} [CommSemiring R] [Semiring A]
variable [StarRing R] [StarRing A] [Algebra R A] [StarModule R A]

/-- A *maximal abelian star subalgebra* (often abbreviated to *masa* or *MASA*) is a commutative
star subalgebra which is maximal with respect to these properties.

This is implemented as an abbreviation for `NonUnitalStarSubalgebra.IsMasa`, but it suffices to
check that the subalgebra is maximal among commutative unital subalgebras. See also
`StarSubalgebra.IsMasa.of_maximal`. -/
abbrev StarSubalgebra.IsMasa (B : StarSubalgebra R A) : Prop :=
  NonUnitalStarSubalgebra.IsMasa B.toNonUnitalStarSubalgebra

instance StarSubalgebra.IsMasa.instIsMulCommutative {B : StarSubalgebra R A} [hB : B.IsMasa] :
    IsMulCommutative B :=
  hB.toIsMulCommutative

/-- If `B` is a (non-unital) masa in a unital star algebra, then `1 ∈ B`, so that `B` is,
in fact, unital. -/
protected lemma NonUnitalStarSubalgebra.IsMasa.one_mem (B : NonUnitalStarSubalgebra R A)
    [hB : B.IsMasa] : (1 : A) ∈ B :=
  letI C := (StarAlgebra.adjoin R (B : Set A)).toNonUnitalStarSubalgebra
  have : B ≤ C := fun _a ha ↦ StarAlgebra.subset_adjoin R (B : Set A) ha
  hB.maximal C this (one_mem (StarAlgebra.adjoin R (B : Set A)))

/-- To show that a commutative unital star subalgebra is a masa, it suffices to check that it is
maximal among commutative *unital* star subalgebras. -/
lemma StarSubalgebra.IsMasa.of_maximal (B : StarSubalgebra R A) [hB : IsMulCommutative B]
    (hC : (∀ C : StarSubalgebra R A, [IsMulCommutative C] → B ≤ C → C ≤ B)) :
    StarSubalgebra.IsMasa B where
  maximal C _ hBC :=
    have : C ≤ (StarAlgebra.adjoin R C).toNonUnitalStarSubalgebra :=
      fun _a ha ↦ StarAlgebra.subset_adjoin R (C : Set A) ha
    this.trans <| hC (StarAlgebra.adjoin R C) (hBC.trans this)

/-- A masa is maximal among commutative star subaglebras. -/
protected lemma StarSubalgebra.IsMasa.maximal {B : StarSubalgebra R A} [hB : B.IsMasa]
    (C : StarSubalgebra R A) [hC : IsMulCommutative C] (hBC : B ≤ C) : C ≤ B :=
  NonUnitalStarSubalgebra.IsMasa.maximal (self := hB) C.toNonUnitalStarSubalgebra hBC

/-- Every commutative star subalgebra is contained in a masa. -/
lemma StarSubalgebra.exists_le_isMasa (B : StarSubalgebra R A) [hB : IsMulCommutative B] :
    ∃ (C : StarSubalgebra R A), B ≤ C ∧ C.IsMasa := by
  obtain ⟨C, hC⟩ := B.toNonUnitalStarSubalgebra.exists_le_isMasa
  exact ⟨C.toStarSubalgebra hC.2.one_mem, hC⟩

/-- A masa in a topological star algebra is closed. -/
instance StarSubalgebra.IsMasa.isClosed [TopologicalSpace A] [IsTopologicalSemiring A]
    [ContinuousStar A] [T2Space A] (B : StarSubalgebra R A)
    [hB : B.IsMasa] : IsClosed (B : Set A) :=
  closure_subset_iff_isClosed.mp <| hB.maximal _ B.le_topologicalClosure

end Unital
