import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic

section IsMulCommutative

variable {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]

@[to_additive]
lemma isMulCommutative_iff : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨IsMulCommutative.mul_comm, IsMulCommutative.of_forall_comm⟩ := isMulCommutative_iff

@[to_additive]
lemma isMulCommutative_iff_of_setLike {s : S} :
    IsMulCommutative s ↔ ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
  simp [isMulCommutative_iff]

@[to_additive]
alias ⟨IsMulCommutative.setLike_mul_comm, IsMulCommutative.of_setLike_mul_comm⟩ :=
  isMulCommutative_iff_of_setLike

instance Algebra.instIsMulCommutativeAdjoin {S R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [SetLike S A] [MulMemClass S A] (s : S) [hs : IsMulCommutative s] :
    IsMulCommutative (adjoin R (s : Set A)) :=
  let := adjoinCommSemiringOfComm R hs.setLike_mul_comm
  ⟨⟨mul_comm⟩⟩

lemma setLike_mul_comm_star {S A : Type*}
    [Semigroup A] [StarMul A] [SetLike S A] [MulMemClass S A] [StarMemClass S A]
    {s : S} [hs : IsMulCommutative s] ⦃a b : A⦄ (ha : a ∈ s) (hb : b ∈ s) :
    a * star b = star b * a :=
  IsMulCommutative.setLike_mul_comm inferInstance a ha (star b) (star_mem hb)

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

@[to_additive]
instance Subsemigroup.instIsMulCommutativeTopologicalClosure {A : Type*}
    [TopologicalSpace A] [Semigroup A] [ContinuousMul A] [T2Space A]
    (s : Subsemigroup A) [hs : IsMulCommutative s] :
    IsMulCommutative s.topologicalClosure :=
  let := s.commSemigroupTopologicalClosure hs.mul_comm
  ⟨⟨mul_comm⟩⟩

@[to_additive]
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

@[to_additive]
theorem Subsemigroup.isMulCommutative_iSup {A : Type*} [Semigroup A] {ι : Type*}
    {S : ι → Subsemigroup A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) : IsMulCommutative (⨆ i, S i : Subsemigroup A) := by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact (hS k).setLike_mul_comm a (hik ha) b (hjk hb)

@[to_additive]
theorem Subgroup.isMulCommutative_iSup {A : Type*} [Group A] {ι : Type*} [Nonempty ι]
    {S : ι → Subgroup A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) : IsMulCommutative (⨆ i, S i : Subgroup A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using Subsemigroup.isMulCommutative_iSup dir

@[to_additive]
theorem Submonoid.isMulCommutative_iSup {A : Type*} [Monoid A] {ι : Type*} [Nonempty ι]
    {S : ι → Submonoid A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) : IsMulCommutative (⨆ i, S i : Submonoid A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using Subsemigroup.isMulCommutative_iSup dir

theorem NonUnitalSubsemiring.isMulCommutative_iSup {A : Type*} [NonUnitalSemiring A]
    {ι : Type*} [Nonempty ι] {S : ι → NonUnitalSubsemiring A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring A) := by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact (hS k).setLike_mul_comm a (hik ha) b (hjk hb)

theorem Subsemiring.isMulCommutative_iSup {A : Type*} [Semiring A] {ι : Type*} [Nonempty ι]
    {S : ι → Subsemiring A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) : IsMulCommutative (⨆ i, S i : Subsemiring A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using Subsemigroup.isMulCommutative_iSup dir

theorem NonUnitalSubring.isMulCommutative_iSup {A : Type*}
    [NonUnitalRing A] {ι : Type*} [Nonempty ι] {S : ι → NonUnitalSubring A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring A) := by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

theorem Subring.isMulCommutative_iSup {A : Type*} [Ring A] {ι : Type*} [Nonempty ι]
    {S : ι → Subring A} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) : IsMulCommutative (⨆ i, S i : Subring A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using Subsemigroup.isMulCommutative_iSup dir

theorem NonUnitalSubalgebra.isMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [Module R A] {ι : Type*} [IsScalarTower R A A]
    [SMulCommClass R A A] [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) := by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

theorem NonUnitalStarSubalgebra.isMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] {ι : Type*} [StarRing R] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) := by
  have := NonUnitalSubsemiring.isMulCommutative_iSup dir
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubsemiring.coe_iSup_of_directed dir]

theorem StarSubalgebra.coe_iSup_of_directed {R A : Type*} [CommSemiring R]
    [Semiring A] [StarRing A] [Algebra R A] {ι : Type*} [StarRing R]
    [StarModule R A] [Nonempty ι] {S : ι → StarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) :=
  let K : StarSubalgebra R A :=
    { __ := NonUnitalStarSubalgebra.copy _ _ (NonUnitalStarSubalgebra.coe_iSup_of_directed
        (S := fun i ↦ (S i).toNonUnitalStarSubalgebra) dir).symm
      algebraMap_mem' x :=
        let ⟨i⟩ := ‹Nonempty ι›
        Set.mem_iUnion.mpr ⟨i, algebraMap_mem (S i) x⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i)
    (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl

theorem Subalgebra.isMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] {ι : Type*} [Nonempty ι] {S : ι → Subalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) := by
  have dir' : Directed (fun x1 x2 ↦ x1 ≤ x2) (fun i ↦ (S i).toNonUnitalSubalgebra) := dir
  have := NonUnitalSubalgebra.isMulCommutative_iSup dir'
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubalgebra.coe_iSup_of_directed dir']

theorem StarSubalgebra.isMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [Semiring A] [StarRing A] [Algebra R A] {ι : Type*} [StarRing R]
    [StarModule R A] [Nonempty ι] {S : ι → StarSubalgebra R A}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (fun x1 x2 ↦ x1 ≤ x2) S) :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) := by
  have dir' : Directed (fun x1 x2 ↦ x1 ≤ x2) (fun i ↦ (S i).toNonUnitalSubalgebra) := dir
  have := NonUnitalSubalgebra.isMulCommutative_iSup dir'
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    NonUnitalSubalgebra.coe_iSup_of_directed dir']

@[to_additive]
instance Subsemigroup.instIsMulCommutative_iSup {A : Type*}
    [Semigroup A] {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subsemigroup A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subsemigroup A) :=
  Subsemigroup.isMulCommutative_iSup S.monotone.directed_le

@[to_additive]
instance Submonoid.instIsMulCommutative_iSup {A : Type*}
    [Monoid A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Submonoid A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Submonoid A) :=
  Submonoid.isMulCommutative_iSup S.monotone.directed_le

@[to_additive]
instance Subgroup.instIsMulCommutative_iSup {A : Type*}
    [Group A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subgroup A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subgroup A) :=
  Subgroup.isMulCommutative_iSup S.monotone.directed_le

instance NonUnitalSubsemiring.instIsMulCommutative_iSup {A : Type*}
    [NonUnitalSemiring A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubsemiring A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring A) :=
  NonUnitalSubsemiring.isMulCommutative_iSup S.monotone.directed_le

instance NonUnitalSubring.instIsMulCommutative_iSup {A : Type*}
    [NonUnitalRing A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubring A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring A) :=
  NonUnitalSubring.isMulCommutative_iSup S.monotone.directed_le

instance Subsemiring.instIsMulCommutative_iSup {A : Type*}
    [Semiring A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subsemiring A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subsemiring A) :=
  Subsemiring.isMulCommutative_iSup S.monotone.directed_le

instance Subring.instIsMulCommutative_iSup {A : Type*}
    [Ring A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subring A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subring A) :=
  Subring.isMulCommutative_iSup S.monotone.directed_le

instance NonUnitalSubalgebra.instIsMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [Module R A] {ι : Type*} [IsScalarTower R A A]
    [SMulCommClass R A A] [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubalgebra R A) :=
  NonUnitalSubalgebra.isMulCommutative_iSup S.monotone.directed_le

theorem NonUnitalStarSubalgebra.instIsMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] {ι : Type*} [StarRing R] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalStarSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarSubalgebra.isMulCommutative_iSup S.monotone.directed_le

instance Subalgebra.instIsMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) :=
  Subalgebra.isMulCommutative_iSup S.monotone.directed_le

theorem StarSubalgebra.instIsMulCommutative_iSup {R A : Type*} [CommSemiring R]
    [Semiring A] [StarRing A] [Algebra R A] {ι : Type*} [StarRing R]
    [StarModule R A] [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o StarSubalgebra R A} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : StarSubalgebra R A) :=
  StarSubalgebra.isMulCommutative_iSup S.monotone.directed_le

namespace IsMulCommutative

variable {R : Type*}

@[to_additive]
instance (priority := 100) [Mul R] [Subsingleton R] : IsMulCommutative R where
  is_comm := ⟨fun _ _ ↦ Subsingleton.elim ..⟩

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

/-- If all elements of `s : Set A` commute pairwise and with elements of `star s`, then `adjoin R s`
is commutative. -/
theorem NonUnitalStarAlgebra.isMulCommutative_adjoin (R : Type*) {A : Type*} [CommSemiring R]
    [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hcomm_star : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a) :
    IsMulCommutative (adjoin R s) := by
  have := adjoin_le_centralizer_centralizer R s
  refine .of_setLike_mul_comm fun _ h₁ _ h₂ ↦ ?_
  have hcomm : ∀ a ∈ s ∪ star s, ∀ b ∈ s ∪ star s, a * b = b * a := fun a ha b hb ↦
    Set.union_star_self_comm (fun _ ha _ hb ↦ hcomm _ hb _ ha)
      (fun _ ha _ hb ↦ hcomm_star _ hb _ ha) b hb a ha
  apply this at h₁
  apply this at h₂
  rw [← SetLike.mem_coe, NonUnitalStarSubalgebra.coe_centralizer_centralizer] at h₁ h₂
  exact Set.centralizer_centralizer_comm_of_comm hcomm _ h₁ _ h₂

attribute [grind →] Commute.eq star_comm_self

open NonUnitalStarAlgebra in
/-- A normal element which commutes with every element of a masa is itself in the masa. -/
theorem NonUnitalStarSubalgebra.IsMasa.mem_of_commute (B : NonUnitalStarSubalgebra R A)
    [hB : IsMasa B] {x : A} [IsStarNormal x] (hx : ∀ y ∈ B, Commute x y) : x ∈ B := by
  let S : NonUnitalStarSubalgebra R A := adjoin R ({x} ∪ B)
  suffices IsMulCommutative S by
    replace hx : x ∈ S := subset_adjoin R _ <| by simp
    exact hB.maximal S (fun y hy ↦ subset_adjoin R _ (by aesop)) hx
  have hx₀ : star x * x = x * star x := star_comm_self' x
  have hx₁ : ∀ y : B, Commute x (star y) := by
    rw [star_involutive.surjective.forall]; simpa using hx
  have hx₂ : ∀ y : B, Commute (star x) y := by simpa [commute_star_comm] using hx₁
  have hB₀ : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := IsMulCommutative.setLike_mul_comm inferInstance
  have hB₁ := setLike_mul_comm_star (s := B)
  refine isMulCommutative_adjoin R ?_ ?_
  all_goals simp [commute_iff_eq] at *; grind

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
    ∃ (C : StarSubalgebra R A), B ≤ C ∧ C.IsMasa :=
  have ⟨C, hC⟩ := B.toNonUnitalStarSubalgebra.exists_le_isMasa
  ⟨C.toStarSubalgebra hC.2.one_mem, hC⟩

/-- A normal element which commutes with every element of a masa is itself in the masa. -/
theorem StarSubalgebra.IsMasa.mem_of_commute (B : StarSubalgebra R A)
    [hB : IsMasa B] {x : A} [IsStarNormal x] (hx : ∀ y ∈ B, Commute x y) : x ∈ B := by
  rw [← mem_toNonUnitalStarSubalgebra]
  exact NonUnitalStarSubalgebra.IsMasa.mem_of_commute B.toNonUnitalStarSubalgebra hx

/-- A masa in a topological star algebra is closed. -/
instance StarSubalgebra.IsMasa.isClosed [TopologicalSpace A] [IsTopologicalSemiring A]
    [ContinuousStar A] [T2Space A] (B : StarSubalgebra R A)
    [hB : B.IsMasa] : IsClosed (B : Set A) :=
  closure_subset_iff_isClosed.mp <| hB.maximal _ B.le_topologicalClosure

end Unital
