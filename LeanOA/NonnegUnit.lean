import Mathlib
import LeanOA.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LeanOA.ForMathlib.Algebra.Star.Unitary
import LeanOA.ForMathlib.Misc

/-! # Relationships between invertibility and nonnegative elements

## Main definitions

+ `unitOfAddNonneg`: the unit obtained by adding a positive scalar to a nonnegative
  element in a C⋆-algebra.
-/

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℝ A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

open scoped NNReal

namespace CFC

/-- The unit obtained by adding a positive scalar to a nonnegative element in a C⋆-algebra. -/
noncomputable def unitOfAddNonneg (r : ℝ≥0) (hr : 0 < r) (a : A) (ha : 0 ≤ a) : Aˣ :=
  cfcUnits (r + ·) a (fun _ _ ↦ by positivity) (by fun_prop)

variable {r : ℝ≥0} {hr : 0 < r} {a : A} {ha : 0 ≤ a}

/-- This is not marked as a `simp` lemma because there may be several rewrite options that are
preferable. -/
lemma val_unitOfAddNonneg :
    (unitOfAddNonneg r hr a ha : A) = cfc (r + ·) a := by
  rfl

/-- This is not marked as a `simp` lemma because there may be several rewrite options that are
preferable. -/
lemma val_inv_unitOfAddNonneg :
    (↑(unitOfAddNonneg r hr a ha)⁻¹ : A) = cfc (fun x ↦ (r + x)⁻¹) a := by
  rfl

lemma val_unitOfAddNonneg_eq_algebraMap_add_self :
    (unitOfAddNonneg r hr a ha : A) = algebraMap ℝ≥0 A r + a := by
  rw [val_unitOfAddNonneg, cfc_add .., cfc_id' .., cfc_const ..]

@[simp]
lemma val_unitOfAddNonneg_nonneg : 0 ≤ (unitOfAddNonneg r hr a ha : A) :=
  cfc_nonneg_of_predicate

@[simp]
lemma val_inv_unitOfAddNonneg_nonneg : 0 ≤ (↑(unitOfAddNonneg r hr a ha)⁻¹ : A) :=
  cfc_nonneg_of_predicate

lemma le_val_unitOfAddNonneg : algebraMap ℝ≥0 A r ≤ unitOfAddNonneg r hr a ha := by
  rw [← add_zero (algebraMap _ _ r), val_unitOfAddNonneg_eq_algebraMap_add_self]
  gcongr

variable [IsTopologicalRing A] [T2Space A]

lemma val_unitOfAddNonneg_eq_cfc_real :
    (unitOfAddNonneg r hr a ha : A) = cfc ((r : ℝ) + ·) a := by
  rw [val_unitOfAddNonneg, cfc_nnreal_eq_real]
  apply cfc_congr fun x hx ↦ ?_
  simpa using spectrum_nonneg_of_nonneg ha hx

lemma val_inv_unitOfAddNonneg_eq_cfc_real :
    (↑(unitOfAddNonneg r hr a ha)⁻¹ : A) = cfc (fun x ↦ ((r : ℝ) + x)⁻¹) a := by
  rw [val_inv_unitOfAddNonneg, cfc_nnreal_eq_real]
  apply cfc_congr fun x hx ↦ ?_
  simpa using spectrum_nonneg_of_nonneg ha hx

end CFC

namespace CStarAlgebra
open CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {r : ℝ≥0} {hr : 0 < r} {a : A} {ha : 0 ≤ a}

lemma val_inv_unitOfAddNonneg_le : (↑(unitOfAddNonneg r hr a ha)⁻¹ : A) ≤ algebraMap ℝ≥0 A r⁻¹ := by
  let u := Units.mk0 r hr.ne' |>.map <| (algebraMap ℝ≥0 A).toMonoidHom
  refine CStarAlgebra.inv_le_inv (a := u) ?_ le_val_unitOfAddNonneg
  simpa [u, Algebra.algebraMap_eq_smul_one] using smul_nonneg (zero_le r) zero_le_one

lemma nnnorm_val_unitOfAddNonneg [Nontrivial A] :
    ‖(unitOfAddNonneg r hr a ha : A)‖₊ = r + ‖a‖₊ := by
  rw [val_unitOfAddNonneg]
  apply IsGreatest.nnnorm_cfc_nnreal (r + ·) a |>.unique
  apply add_left_mono.map_isGreatest
  simpa [cfc_id ℝ≥0 a ha] using IsGreatest.nnnorm_cfc_nnreal id a

lemma norm_val_unitOfAddNonneg [Nontrivial A] :
    ‖(unitOfAddNonneg r hr a ha : A)‖ = r + ‖a‖ :=
  congr($(nnnorm_val_unitOfAddNonneg).toReal)

end CStarAlgebra
