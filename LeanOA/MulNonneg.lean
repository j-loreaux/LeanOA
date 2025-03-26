import Mathlib
import LeanOA.CFCRange

/-! # Product of commuting nonnegative elements is nonnnegative -/

open scoped NNReal

namespace CFC

-- it seems like some of the hypotheses are wrong near `CFC.sqrt`.
variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [StarRing A]
    [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [TopologicalSpace A]
    [T2Space A] [IsTopologicalRing A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

lemma sqrt_eq_cfcₙ_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)), ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  exact cfcₙ_congr (Real.mul_self_sqrt <| quasispectrum_nonneg_of_nonneg a ha · ·)

end CFC

namespace CStarAlgebra

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

lemma _root_.Commute.mul_nonneg {a b : A} (hab : Commute a b)
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    0 ≤ a * b := by
  rw [← CFC.sqrt_mul_sqrt_self a, CFC.sqrt_eq_cfcₙ_real_sqrt a, mul_assoc,
    (ha.isSelfAdjoint.commute_cfcₙ hab Real.sqrt).eq, ← mul_assoc, ← CFC.sqrt_eq_cfcₙ_real_sqrt a]
  exact conjugate_nonneg_of_nonneg hb CFC.sqrt_nonneg

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma prod_nonneg_of_commute {l : List A} (hl_nonneg : ∀ x ∈ l, 0 ≤ x) (hl_comm : ∀ x ∈ l, ∀ y ∈ l, Commute x y) :
    0 ≤ l.prod := by
  induction l with
  | nil => exact zero_le_one
  | cons x xs ih =>
    simp only [List.prod_cons]
    simp only [List.mem_cons, forall_eq_or_imp, Commute.refl, true_and] at hl_nonneg hl_comm
    refine Commute.list_prod_right _ _ hl_comm.1 |>.mul_nonneg hl_nonneg.1 ?_
    refine ih hl_nonneg.2 ?_
    peel hl_comm.2 with x hx _
    exact this.2

end Unital

end CStarAlgebra
