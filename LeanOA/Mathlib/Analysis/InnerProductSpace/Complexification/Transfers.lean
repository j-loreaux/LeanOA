module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import LeanOA.Mathlib.Analysis.InnerProductSpace.Complexification.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Transfering results from C⋆-algebras to `𝕜` and `ℝ` Hilbert spaces via complexification

In particular, we provide the continuous functional calculus for `Eₗ →L[ℝ] Eₗ`
(see `ContinuousLinearMap.instCFCReal` and `ContinuousLinearMap.instIsometricCFCReal`). -/

public section

namespace ContinuousLinearMap
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

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

lemma conjugateStarAlgEquiv_comp_cfcHom_toComplexification {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) :
    (conjugateStarAlgEquiv).toStarAlgHom.comp (cfcHom hT.toComplexification) =
      cfcHom hT.toComplexification := by
  refine symm <| cfcHom_eq_of_continuous_of_map_id hT.toComplexification _ ?_ ?_
  · eta_expand
    simp only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply, conjugateStarAlgEquiv_apply]
    fun_prop
  · simp [cfcHom_id hT.toComplexification, conjugateStarAlgEquiv_apply]

theorem conjugate_cfcHom_toComplexification {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcHom hT.toComplexification g).conjugate = cfcHom hT.toComplexification g := by
  conv_lhs => rw [← conjugateStarAlgEquiv_comp_cfcHom_toComplexification hT]
  simp [conjugateStarAlgEquiv_apply]

lemma commute_cfcHom_mulI [NormedSpace ℝ E] (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    Commute (cfcHom hT.toComplexification g)
      ((RCLike.I : 𝕜) • (1 : E →L[𝕜] E)).toComplexification := by
  refine hT.toComplexification.commute_cfcHom _ ?_ g
  simp [commute_iff_eq, ContinuousLinearMap.ext_iff]

attribute [local simp] toComplexification_ofComplexificationK conjugate_cfcHom_toComplexification in
/-- The real star algebra homomorphism between `C(spectrum ℝ T.toComplexification, ℝ)` and
`Eₗ →L[ℝ] Eₗ`.
This is used in the continuous functional calculus. -/
private noncomputable def cfcRealHomAux [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) : C(spectrum ℝ T.toComplexification, ℝ) →⋆ₐ[ℝ] (E →L[𝕜] E) where
  toFun g := (cfcHom hT.toComplexification g).ofComplexificationK 𝕜 (commute_cfcHom_mulI T hT _)
  map_one' := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by simp [← toComplexification_inj, hT]
  map_star' _ := by simp [← toComplexification_inj, hT, ← star_toComplexification, ← map_star]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

private lemma toComplexification_cfcRealHomAux [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (g : C(spectrum ℝ T.toComplexification, ℝ)) :
    (cfcRealHomAux hT g).toComplexification = cfcHom hT.toComplexification g := by
  refine toComplexification_ofComplexificationK ?_ (conjugate_cfcHom_toComplexification hT g)
  exact commute_cfcHom_mulI T hT g

instance [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (a : E →L[𝕜] E) :
    CompactSpace ↑(spectrum ℝ a) := by
  rw [← spectrum_toComplexification_real]
  infer_instance

instance instCFC [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint where
  predicate_zero := IsSelfAdjoint.zero _
  spectrum_nonempty T hT := by
    rw [← spectrum_toComplexification_real]
    have : Nontrivial (Complexification 𝕜 E →L[ℂ] Complexification 𝕜 E) :=
      toComplexification_injective.nontrivial
    exact ContinuousFunctionalCalculus.spectrum_nonempty _ hT.toComplexification
  exists_cfc_of_predicate T hT := by
    rw [← spectrum_toComplexification_real]
    refine ⟨cfcRealHomAux hT, ?_, fun x y hxy ↦ ?_, ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · rw [isometry_toComplexification.isEmbedding.continuous_iff]
      eta_expand
      simp only [Function.comp_apply, toComplexification_cfcRealHomAux]
      fun_prop
    · rwa [← toComplexification_inj, toComplexification_cfcRealHomAux,
        toComplexification_cfcRealHomAux, (cfcHom_injective hT.toComplexification).eq_iff] at hxy
    · rw [← toComplexification_inj, toComplexification_cfcRealHomAux, cfcHom_id ..]
    · rw [← spectrum_toComplexification_real, toComplexification_cfcRealHomAux]
      exact cfcHom_map_spectrum ..
    · rw [← isSelfAdjoint_toComplexification_iff, toComplexification_cfcRealHomAux]
      exact cfcHom_predicate ..

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

instance instIsometricCFCReal [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint where
  isometric T hT := (AddMonoidHomClass.isometry_iff_norm _).mpr fun x ↦ by
    suffices ‖cfcHom hT x‖₊ = ‖x‖₊ from congr($this)
    have : IsSelfAdjoint (cfcHom hT x) := cfcHom_predicate ..
    simp_rw [← ENNReal.coe_inj, ← spectralRadius_eq_opNNNorm this,
      ← spectralRadius_toComplexification this,
      ← this.toComplexification.spectrumRestricts.spectralRadius_eq,
      spectralRadius, ← enorm_eq_nnnorm, ContinuousMap.enorm_eq_iSup_enorm]
    rw [← iSup_range, ← cfcHom_map_spectrum hT, spectrum_toComplexification_real]

-- just make `ContinuousLinearMap.instStarOrderedRingRCLike` an instance instead?
instance [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    StarOrderedRing (E →L[𝕜] E) := ContinuousLinearMap.instStarOrderedRingRCLike

end ContinuousLinearMap
