import Mathlib.Analysis.CStarAlgebra.Module.Defs

/-!

# Main declarations

+ `CStarModule.polarization`: The polarization identity for C⋆-modules.
-/

open scoped InnerProductSpace

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable [NormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]

open Complex

namespace CStarModule

lemma polarization {x y : E} :
    4 • ⟪y, x⟫_A = ⟪x + y, x + y⟫_A - ⟪x - y, x - y⟫_A +
      I • ⟪x + I • y, x + I • y⟫_A - I • ⟪x - I • y, x - I • y⟫_A := by
  simp [smul_smul, smul_sub]
  abel

lemma polarization' {x y : E} :
    ⟪y, x⟫_A = (1 / 4 : ℂ) • (⟪x + y, x + y⟫_A - ⟪x - y, x - y⟫_A +
      I • ⟪x + I • y, x + I • y⟫_A - I • ⟪x - I • y, x - I • y⟫_A) := by
  rw [← (IsUnit.mk0 (4 : ℂ) (by norm_num)).smul_left_cancel, ofNat_smul_eq_nsmul ℂ 4]
  simpa only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, smul_inv_smul₀]
    using CStarModule.polarization

end CStarModule
