import Mathlib.Analysis.VonNeumannAlgebra.Basic

open ComplexOrder ContinuousLinearMap VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

abbrev VonNeumannAlgebra.IsStarProjection.range {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    letI := hp.isIdempotentElem.isClosed_range.completeSpace_coe
    VonNeumannAlgebra p.range := by
  letI := hp.isIdempotentElem.isClosed_range.completeSpace_coe
  refine
    { carrier := { x ∘L p.range.subtypeL | x },
      mul_mem' := by
        rintro a b ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a ∘L p.range.subtypeL ∘L b, rfl⟩,
      add_mem' := by
        rintro a b ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, rfl⟩,
      star_mem' := by
        rintro a ⟨a, rfl⟩
        use p.range.orthogonalProjection ∘L (adjoint a) ∘L p.range.orthogonalProjection
        simp [star_eq_adjoint, adjoint_comp, Submodule.adjoint_subtypeL,
          ContinuousLinearMap.ext_iff],
      zero_mem' := ⟨0, rfl⟩,
      one_mem' := ⟨p.range.orthogonalProjection, by
        simp [ContinuousLinearMap.ext_iff]⟩,
      algebraMap_mem' r := ⟨r • p.range.orthogonalProjection, by ext; simp⟩,
      centralizer_centralizer' := ?_ }
  ext a
  refine ⟨fun h ↦ ?_, ?_⟩
  · use a ∘L p.range.orthogonalProjection
    simp [ContinuousLinearMap.ext_iff]
  · rintro ⟨a, rfl⟩ b hb
    exact hb (a ∘L p.range.subtypeL) (by simp) |>.symm
