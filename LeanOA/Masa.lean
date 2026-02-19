import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

variable {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
  [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm (a b : B)  : a * b = b * a
  maximal (C : NonUnitalStarSubalgebra R A) (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
      (hBC : B ≤ C) : C ≤ B

theorem exists_le_masa
  (B : {C : NonUnitalStarSubalgebra R A // (∀ x ∈ C, ∀ y ∈ C, x * y = y * x)}) :
    ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa  := by
  have := by
    refine zorn_le (α := {C : NonUnitalStarSubalgebra R A //
      (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ B ≤ C}) ?_
    intro chain hchain
    obtain (rfl | h) := chain.eq_empty_or_nonempty
    · exact ⟨⟨B.val, B.prop, le_rfl⟩, by simp⟩
    · have := h.to_subtype
      have hdir : Directed (· ≤ ·) fun S : chain ↦ S.val.val :=
        hchain.directedOn.directed_val.mono_comp _ (by simp)
      let bound : NonUnitalStarSubalgebra R A := ⨆ S : chain, S.val.val
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
  obtain ⟨M, M1⟩ := this
  use M.1
  constructor
  · exact M.2.2
  · constructor
    · simpa using M.2.1
    · dsimp [IsMax] at M1
      intro C hC hBC
      simp_all only [Subtype.forall, forall_and_index]
      obtain ⟨b, hb⟩ := B
      obtain ⟨m , hm⟩ := M
      obtain ⟨left, right⟩ := hm
      simp_all only [Subtype.mk_le_mk, implies_true]
      simp_all only [implies_true, le_refl]
      apply M1 C hC
      · exact NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.mp fun ⦃x⦄ a ↦ hBC (right a)
      · exact NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff.mp hBC
