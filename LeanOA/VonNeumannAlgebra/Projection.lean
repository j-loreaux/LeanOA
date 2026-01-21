import Mathlib.Analysis.VonNeumannAlgebra.Basic

open ComplexOrder ContinuousLinearMap VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

@[simp] theorem IsStarProjection.starProjection_range_eq {p : H →L[ℂ] H} (hp : IsStarProjection p)
    [p.range.HasOrthogonalProjection] : p.range.starProjection = p :=
  have ⟨_, h⟩ := (isStarProjection_iff_eq_starProjection_range.mp hp)
  h.symm

@[simp] theorem IsStarProjection.rangeRestrict_eq_orthogonalProjection_range
    {p : H →L[ℂ] H} (hp : IsStarProjection p) [p.range.HasOrthogonalProjection] :
    p.range.orthogonalProjection = p.rangeRestrict := by
  ext x
  have := congr($hp.starProjection_range_eq x)
  rw [← Submodule.coe_orthogonalProjection_apply] at this
  simp [← this]

/-- `pMp` is a vN algebra when `p` is a star projection. -/
abbrev VonNeumannAlgebra.IsStarProjection.range {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) :
    letI : CompleteSpace p.range := hp.isIdempotentElem.isClosed_range.completeSpace_coe
    VonNeumannAlgebra p.range := by
  letI : CompleteSpace p.range := hp.isIdempotentElem.isClosed_range.completeSpace_coe
  refine
    { carrier := { p.range.orthogonalProjection ∘L x ∘L p.range.subtypeL | x ∈ M }
      mul_mem' := by
        rintro a b ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        refine ⟨a * p * b, mul_mem (mul_mem ha hpM) hb, by ext; simp [hp]⟩
      add_mem' := by
        rintro a b ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        refine ⟨a + b, add_mem ha hb, by simp⟩
      star_mem' := by
        rintro a ⟨a, ha, rfl⟩
        refine ⟨p * star a * p, mul_mem (mul_mem hpM (star_mem ha)) hpM, ?_⟩
        simp only [star_eq_adjoint, adjoint_comp, Submodule.adjoint_subtypeL,
          Submodule.adjoint_orthogonalProjection, ContinuousLinearMap.ext_iff, coe_comp', coe_mul,
          Submodule.coe_subtypeL', Submodule.coe_subtype, Function.comp_apply, Subtype.forall,
          LinearMap.mem_range, coe_coe, forall_exists_index, forall_apply_eq_imp_iff]
        intro x
        rw [← Subtype.coe_inj]
        simp [← mul_apply p p, hp.isIdempotentElem.eq, hp]
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      one_mem' := by
        refine ⟨p, hpM, ?_⟩
        simp only [ContinuousLinearMap.ext_iff, coe_comp', Submodule.coe_subtypeL',
          Submodule.coe_subtype, Function.comp_apply, one_apply, Subtype.forall,
          LinearMap.mem_range, coe_coe, forall_exists_index]
        rintro a x rfl
        rw [← Subtype.coe_inj]
        simp [hp, ← mul_apply p p, hp.isIdempotentElem.eq]
      algebraMap_mem' r := by
        refine ⟨r • p, StarSubalgebra.smul_mem _ hpM _, ?_⟩
        simp [hp, ContinuousLinearMap.ext_iff, ← Subtype.coe_inj, ← mul_apply p p,
          hp.isIdempotentElem.eq]
      centralizer_centralizer' := ?_ }
  ext a
  refine ⟨?_, ?_⟩
  · sorry
  · rintro ⟨a, ha, rfl⟩ b hb
    have := by simpa using Set.mem_centralizer_iff.mp hb
    exact this a ha |>.symm
