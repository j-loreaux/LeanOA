import LeanOA.Ultraweak.Basic
import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Transfer
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

set_option backward.isDefEq.respectTransparency false

variable {M P : Type*}

namespace Ultraweak

open scoped NNReal

section NonUnital

variable [NonUnitalCStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

instance : NonUnitalContinuousFunctionalCalculus ℂ σ(M, P) IsStarNormal :=
  .transfer (starAlgEquiv M P).symm continuous_toUltraweak (fun _ ↦ Iff.rfl)

instance : NonUnitalContinuousFunctionalCalculus ℝ σ(M, P) IsSelfAdjoint :=
  .transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ) continuous_toUltraweak (fun _ ↦ Iff.rfl)

@[simp]
lemma toUltraweak_cfcₙ_complex (f : ℂ → ℂ) (m : M) :
    toUltraweak ℂ P (cfcₙ f m) = cfcₙ f (toUltraweak ℂ P m) :=
  Eq.symm <| cfcₙ_eq_cfcₙ_transfer (starAlgEquiv M P).symm
    continuous_toUltraweak (fun _ ↦ Iff.rfl) ..

@[simp]
lemma ofUltraweak_cfcₙ_complex (f : ℂ → ℂ) (m : σ(M, P)) :
    ofUltraweak (cfcₙ f m) = cfcₙ f (ofUltraweak m) :=
  congr(ofUltraweak $(toUltraweak_cfcₙ_complex f (ofUltraweak m) (P := P))).symm

@[simp]
lemma toUltraweak_cfcₙ_real (f : ℝ → ℝ) (m : M) :
    toUltraweak ℂ P (cfcₙ f m) = cfcₙ f (toUltraweak ℂ P m) :=
  Eq.symm <| cfcₙ_eq_cfcₙ_transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ)
    continuous_toUltraweak (fun _ ↦ Iff.rfl) ..

@[simp]
lemma ofUltraweak_cfcₙ_real (f : ℝ → ℝ) (m : σ(M, P)) :
    ofUltraweak (cfcₙ f m) = cfcₙ f (ofUltraweak m) :=
  congr(ofUltraweak $(toUltraweak_cfcₙ_real f (ofUltraweak m) (P := P))).symm

variable [PartialOrder M] [StarOrderedRing M]

instance : NonUnitalContinuousFunctionalCalculus ℝ≥0 σ(M, P) (0 ≤ ·) :=
  .transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ≥0) continuous_toUltraweak (fun _ ↦ Iff.rfl)

/- The lemmas `{to,of}Ultraweak_cfcₙ_nnreal` require a `ContinuousMapZero.UniqueHom ℝ≥0 σ(M, P)`
instace, which requires that `σ(M, P)` is a topological algebra. So, we cannot establish those
until we first show that multiplication is continuous in each variable separately. -/

end NonUnital

section Unital

variable [CStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

instance : ContinuousFunctionalCalculus ℂ σ(M, P) IsStarNormal :=
  .transfer (starAlgEquiv M P).symm continuous_toUltraweak (fun _ ↦ Iff.rfl)

instance : ContinuousFunctionalCalculus ℝ σ(M, P) IsSelfAdjoint :=
  .transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ) continuous_toUltraweak (fun _ ↦ Iff.rfl)

@[simp]
lemma toUltraweak_cfc_complex (f : ℂ → ℂ) (m : M) :
    toUltraweak ℂ P (cfc f m) = cfc f (toUltraweak ℂ P m) :=
  Eq.symm <| cfc_eq_cfc_transfer (starAlgEquiv M P).symm
    continuous_toUltraweak (fun _ ↦ Iff.rfl) ..

@[simp]
lemma ofUltraweak_cfc_complex (f : ℂ → ℂ) (m : σ(M, P)) :
    ofUltraweak (cfc f m) = cfc f (ofUltraweak m) :=
  congr(ofUltraweak $(toUltraweak_cfc_complex f (ofUltraweak m) (P := P))).symm

@[simp]
lemma toUltraweak_cfc_real (f : ℝ → ℝ) (m : M) :
    toUltraweak ℂ P (cfc f m) = cfc f (toUltraweak ℂ P m) :=
  Eq.symm <| cfc_eq_cfc_transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ)
    continuous_toUltraweak (fun _ ↦ Iff.rfl) ..

@[simp]
lemma ofUltraweak_cfc_real (f : ℝ → ℝ) (m : σ(M, P)) :
    ofUltraweak (cfc f m) = cfc f (ofUltraweak m) :=
  congr(ofUltraweak $(toUltraweak_cfc_real f (ofUltraweak m) (P := P))).symm

variable [PartialOrder M] [StarOrderedRing M]

instance : ContinuousFunctionalCalculus ℝ≥0 σ(M, P) (0 ≤ ·) :=
  .transfer ((starAlgEquiv M P).symm.restrictScalars' ℝ≥0) continuous_toUltraweak (fun _ ↦ Iff.rfl)

/- The lemmas `{to,of}Ultraweak_cfc_nnreal` require a `ContinuousMap.UniqueHom ℝ≥0 σ(M, P)`
instace, which requires that `σ(M, P)` is a topological algebra. So, we cannot establish those
until we first show that multiplication is continuous in each variable separately. -/

end Unital

end Ultraweak
