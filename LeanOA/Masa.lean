import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.CStarAlgebra.Classes

section NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

/-- Maximal abelian star subalgebra (MASA). -/
class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  maximal (C : NonUnitalStarSubalgebra R A) (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
      (hBC : B ≤ C) : C ≤ B

omit [StarRing R] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] in
/-- To check that a commutative `NonUnitalStarSubalgebra` is a masa, it suffices to show that
it contains every commutative `NonUnitalStarSubalgebra`. -/
lemma IsMasa_of_comm_NonUnitalStarSubalg_le (B : NonUnitalStarSubalgebra R A)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hC : ∀ C : NonUnitalStarSubalgebra R A, (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) → C ≤ B) :
    NonUnitalStarSubalgebra.IsMasa B := ⟨hB, fun _ hC1 _ ↦ hC _ hC1⟩

theorem NonUnitalStarSubalgebra.exists_le_isMasa (B : NonUnitalStarSubalgebra R A)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
      ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa := by
  obtain ⟨C, hC⟩ := by
    apply zorn_le (α := {C : NonUnitalStarSubalgebra R A //
      (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ B ≤ C})
    intro chain hchain
    obtain (rfl | h) := chain.eq_empty_or_nonempty
    · exact ⟨⟨B, hB, le_rfl⟩, by simp⟩
    · have := h.to_subtype
      have hdir : Directed (· ≤ ·) fun S : chain ↦ S.val.val :=
        hchain.directedOn.directed_val.mono_comp _ (by simp)
      let bound : NonUnitalStarSubalgebra R A := ⨆ S : chain, S
      refine ⟨⟨bound, ?_, ?_⟩, ?_⟩
      · simp only [bound]
        intro a ha b hb
        rw [← SetLike.mem_coe, NonUnitalStarSubalgebra.coe_iSup_of_directed hdir,
          Set.mem_iUnion] at ha hb
        obtain ⟨S, hS⟩ := ha
        obtain ⟨T, hT⟩ := hb
        obtain ⟨V, hV, hSV, hTV⟩ := hchain.directedOn _ S.prop _ T.prop
        exact V.prop.1 _ (hSV hS) _ (hTV hT)
      · exact Classical.arbitrary chain |>.val.prop.2 |>.trans <|
          le_iSup (fun S : chain ↦ S.val.val) _
      · intro S hS
        lift S to chain using hS
        exact le_iSup (fun S : chain ↦ S.val.val) _
  exact ⟨C, C.prop.2, ⟨C.prop.1, fun S h_comm hCS ↦ @hC ⟨S, h_comm, C.prop.2.trans hCS⟩ hCS⟩⟩

end NonUnitalStarSubalgebra
section TopologicalAlgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
variable [StarRing A] [TopologicalSpace A] [IsTopologicalRing A] (B : NonUnitalStarSubalgebra R A)
variable [ContinuousConstSMul R A] [ContinuousStar A] [T2Space A]

theorem NonUnitalStarSubalgebra.IsMasa.isClosed (B : NonUnitalStarSubalgebra R A) (hB : B.IsMasa) :
    IsClosed (B : Set A) := closure_subset_iff_isClosed.mp <| by
  refine hB.maximal _ ?_ B.le_topologicalClosure
  let h := B.nonUnitalCommSemiringTopologicalClosure <| by simpa using hB.comm
  simpa using mul_comm (G := B.topologicalClosure)

end TopologicalAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*}

instance [NonUnitalCStarAlgebra A] {B : NonUnitalStarSubalgebra ℂ A} [hB : B.IsMasa] :
    NonUnitalCommCStarAlgebra B :=
  { NonUnitalStarSubalgebra.nonUnitalCStarAlgebra B
    (h_closed := NonUnitalStarSubalgebra.IsMasa.isClosed B hB) with
    mul_comm := by simpa using hB.comm }


variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

end NonUnitalCStarAlgebra

section Unital

variable {R A : Type*} [CommSemiring R] [Semiring A]
variable [StarRing R] [StarRing A] [Algebra R A] [StarModule R A]

/-- Unital version as abbrev. -/
abbrev StarSubalgebra.IsMasa (B : StarSubalgebra R A) : Prop :=
  NonUnitalStarSubalgebra.IsMasa B.toNonUnitalStarSubalgebra

--omit [StarRing R] [StarModule R A] in
lemma IsMasa_of_comm_StarSubalg_le (B : StarSubalgebra R A)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hC : ∀ C : StarSubalgebra R A, (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) → C ≤ B) :
    StarSubalgebra.IsMasa B := by
  refine IsMasa_of_comm_NonUnitalStarSubalg_le B.toNonUnitalStarSubalgebra hB ?_
  intro C hCcomm
  set C' := NonUnitalStarSubalgebra.toStarSubalgebra _ (StarSubalgebra.one_mem_toNonUnitalStarSubalgebra
        (StarAlgebra.adjoin (R := R) {x : A | x ∈ C ∨ x = 1}))
  have : C ≤ C'.toNonUnitalStarSubalgebra := by
    grw [← NonUnitalStarSubalgebra.toStarSubalgebra_toNonUnitalStarSubalgebra C]
    congr!
  have : C'.toNonUnitalStarSubalgebra ≤ B.toNonUnitalStarSubalgebra := by
    apply hC
    intro a
    by_cases hh : a = 1
    · rw [hh]
      intro hh1 b hb
      simp only [one_mul, mul_one]
    · sorry

lemma StarSubalgebra.exists_le_isMasa (B : StarSubalgebra R A)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : ∃ (C : StarSubalgebra R A), B ≤ C ∧ C.IsMasa := by
  obtain ⟨C , hC⟩ := NonUnitalStarSubalgebra.exists_le_isMasa (B.toNonUnitalStarSubalgebra) hB
  use NonUnitalStarSubalgebra.toStarSubalgebra _ (NonUnitalStarSubalgebra.mem_carrier.mp
      (hC.1 (StarSubalgebra.one_mem_toNonUnitalStarSubalgebra _)))
  exact And.comm.mp (id (And.symm hC))

end Unital
