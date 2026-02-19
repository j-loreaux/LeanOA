import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.CStarAlgebra.Classes

section NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  maximal (C : NonUnitalStarSubalgebra R A) (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
      (hBC : B ≤ C) : C ≤ B

theorem exists_le_masa (B : {C : NonUnitalStarSubalgebra R A //
  (∀ x ∈ C, ∀ y ∈ C, x * y = y * x)}) :
    ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa  := by
  obtain ⟨C, hC⟩ := by
    apply zorn_le (α := {C : NonUnitalStarSubalgebra R A //
      (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ B ≤ C})
    intro chain hchain
    obtain (rfl | h) := chain.eq_empty_or_nonempty
    · exact ⟨⟨B.val, B.prop, le_rfl⟩, by simp⟩
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

theorem masa_closed (B : NonUnitalStarSubalgebra R A) (hB : B.IsMasa) :
    IsClosed (B : Set A) := by
  rw [← closure_subset_iff_isClosed]
  refine hB.maximal _ ?_ B.le_topologicalClosure
  let h := B.nonUnitalCommSemiringTopologicalClosure <| by simpa using hB.comm
  simpa using mul_comm (G := B.topologicalClosure)

end TopologicalAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*}

theorem isClosed_of_masa_of_nonUnitalCStarAlgebra [NonUnitalCStarAlgebra A]
    (B : NonUnitalStarSubalgebra ℂ A) (hB : B.IsMasa) : IsClosed (B : Set A) := masa_closed B hB

instance [NonUnitalCStarAlgebra A] {B : NonUnitalStarSubalgebra ℂ A} [hB : B.IsMasa] :
    NonUnitalCStarAlgebra B :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra B (h_closed := masa_closed B hB)

end NonUnitalCStarAlgebra
