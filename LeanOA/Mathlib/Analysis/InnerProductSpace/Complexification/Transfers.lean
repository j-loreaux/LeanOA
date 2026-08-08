module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Projection
public import LeanOA.Mathlib.Analysis.InnerProductSpace.Complexification.Basic

/-! Transfering results from C⋆-algebras to `𝕜` and `ℝ` Hilbert spaces via complexification

In particular, we provide the continuous functional calculus for `Eₗ →L[ℝ] Eₗ`
(see `ContinuousLinearMap.instCFCReal` and `ContinuousLinearMap.instIsometricCFCReal`). -/

public section

namespace ContinuousLinearMap
variable {𝕜 E Eₗ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ] [CompleteSpace Eₗ]

open Complexification

protected lemma IsSelfAdjoint.norm_add_eq_max {S T : E →L[𝕜] E}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (h : S * T = 0) :
    ‖S + T‖ = max ‖S‖ ‖T‖ := by
  rw [← opNorm_toComplexification (S + T), map_add,
    hS.toComplexification.norm_add_eq_max hT.toComplexification
      (by simp [← toComplexification_mul, h])]
  simp

/-- `Complexification.conjugate` as a real star algebra equivalence. -/
@[expose] noncomputable def conjugateStarAlgEquiv :
    (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) ≃⋆ₐ[ℝ]
      (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) where
  __ := conjugate.toAddEquiv
  map_mul' := by simp
  map_star' := by simp
  map_smul' _ _ := by ext <;> simp [conj_apply]

lemma conjugateStarAlgEquiv_apply (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :
    conjugateStarAlgEquiv T = T.conjugate := rfl

lemma symm_conjugateStarAlgEquiv_apply (T : Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :
    conjugateStarAlgEquiv.symm T = conjugate.symm T := rfl

lemma conjugateStarAlgEquiv_comp_cfcHom_toComplexification {T : Eₗ →L[ℝ] Eₗ}
    (hT : IsSelfAdjoint T) :
    (conjugateStarAlgEquiv).toStarAlgHom.comp (cfcHom hT.toComplexification) =
      cfcHom hT.toComplexification := by
  refine symm <| cfcHom_eq_of_continuous_of_map_id hT.toComplexification _ ?_ ?_
  · eta_expand
    simp only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply, conjugateStarAlgEquiv_apply]
    fun_prop
  · simp [cfcHom_id hT.toComplexification, conjugateStarAlgEquiv_apply]

theorem conjugate_cfcHom_toComplexification {T : Eₗ →L[ℝ] Eₗ} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcHom hT.toComplexification g).conjugate = cfcHom hT.toComplexification g := by
  conv_lhs => rw [← conjugateStarAlgEquiv_comp_cfcHom_toComplexification hT]
  simp [conjugateStarAlgEquiv_apply]

attribute [local simp] toComplexification_ofComplexification conjugate_cfcHom_toComplexification in
/-- The real star algebra homomorphism between `C(spectrum ℝ T.toComplexification, ℝ)` and
`Eₗ →L[ℝ] Eₗ`.
This is used in the continuous functional calculus. -/
private noncomputable def cfcRealHomAux {T : Eₗ →L[ℝ] Eₗ}
    (hT : IsSelfAdjoint T) : C(spectrum ℝ T.toComplexification, ℝ) →⋆ₐ[ℝ] (Eₗ →L[ℝ] Eₗ) where
  toFun g := (cfcHom hT.toComplexification g).ofComplexification
  map_one' := by simp [← toComplexification_inj]
  map_zero' := by simp [← toComplexification_inj]
  map_add' _ _ := by simp [← toComplexification_inj, hT]
  map_mul' _ _ := by simp [← toComplexification_inj, hT]
  map_star' _ := by simp [← toComplexification_inj, hT, ← star_toComplexification, ← map_star]
  commutes' _ := by
    rw [← toComplexification_inj, toComplexification_ofComplexification (by simp [hT])]
    ext <;> simp [Algebra.algebraMap_eq_smul_one]

private lemma toComplexification_cfcRealHomAux {T : Eₗ →L[ℝ] Eₗ} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcRealHomAux hT g).toComplexification = cfcHom hT.toComplexification g :=
  toComplexification_ofComplexification (conjugate_cfcHom_toComplexification hT g)

instance instCFCReal : ContinuousFunctionalCalculus ℝ (Eₗ →L[ℝ] Eₗ) IsSelfAdjoint where
  predicate_zero := IsSelfAdjoint.zero _
  spectrum_nonempty T hT := by
    rw [← spectrum_toComplexification_real]
    have : Nontrivial (Complexification ℝ Eₗ →L[ℂ] Complexification ℝ Eₗ) :=
      toComplexification_injective.nontrivial
    exact ContinuousFunctionalCalculus.spectrum_nonempty _ hT.toComplexification
  exists_cfc_of_predicate T hT := by
    rw [← spectrum_toComplexification_real]
    refine ⟨cfcRealHomAux hT, ?_, fun x y hxy ↦ ?_, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · rw [isometry_toComplexification.isEmbedding.continuous_iff]
      eta_expand
      simp only [Function.comp_apply, toComplexification_cfcRealHomAux]
      fun_prop
    · rw [← toComplexification_inj] at hxy
      simpa [cfcRealHomAux, toComplexification_ofComplexification,
        conjugate_cfcHom_toComplexification, hT,
        (cfcHom_injective hT.toComplexification).eq_iff] using hxy
    · ext; simp [cfcRealHomAux, cfcHom_id]
    · rw [← spectrum_toComplexification_real, toComplexification_cfcRealHomAux]
      exact cfcHom_map_spectrum hT.toComplexification x
    · simp [isSelfAdjoint_iff, ← map_star]

-- golf of `ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`:
lemma IsIdempotentElem.isSelfAdjoint_iff_isStarNormal' {T : E →L[𝕜] E}
    (hT : IsIdempotentElem T) : IsSelfAdjoint T ↔ IsStarNormal T := by
  rw [← isSelfAdjoint_toComplexification_iff, ← isStarNormal_toComplexification_iff,
    hT.toComplexification.isSelfAdjoint_iff_isStarNormal]

-- golf of `ContinuousLinearMap.spectralRadius_eq_nnnorm`:
lemma spectralRadius_eq_opNNNorm {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  nontriviality E
  refine le_antisymm (spectrum.spectralRadius_le_nnnorm T) ?_
  rw [← opNNNorm_toComplexification, ← hT.toComplexification.spectralRadius_eq_nnnorm,
    ← hT.toComplexification.spectrumRestricts.spectralRadius_eq]
  simp only [spectralRadius, spectrum_toComplexification, Set.mem_preimage, iSup₂_le_iff]
  exact fun r hr ↦ le_iSup₂_of_le _ hr (by simp)

lemma spectralRadius_toComplexification {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) : spectralRadius ℂ T.toComplexification = spectralRadius 𝕜 T := by
  simp [hT.toComplexification.spectralRadius_eq_nnnorm, spectralRadius_eq_opNNNorm hT]

instance instIsometricCFCReal :
    IsometricContinuousFunctionalCalculus ℝ (Eₗ →L[ℝ] Eₗ) IsSelfAdjoint where
  isometric T hT := (AddMonoidHomClass.isometry_iff_norm _).mpr fun x ↦ by
    suffices ‖cfcHom hT x‖₊ = ‖x‖₊ from congr($this)
    simp_rw [← ENNReal.coe_inj, ← spectralRadius_eq_opNNNorm (cfcHom_predicate hT _),
      spectralRadius, cfcHom_map_spectrum, iSup_range, ← enorm_eq_nnnorm,
      ContinuousMap.enorm_eq_iSup_enorm]

end ContinuousLinearMap
