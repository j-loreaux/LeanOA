module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Tactic.Module

@[expose] public section

attribute [fun_prop] CFC.continuous_abs

section PosPartRetract

variable {A : Type*}

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

/-- The function `a ↦ 2⁻¹ • (|a| + a)`. On selfadjoint elements, it coincides with `a⁺`, but it
is globally continuous. -/
noncomputable def CFC.posPartRetract (a : A) : A := (2 : ℝ)⁻¹ • (abs a + a)

@[grind =]
lemma IsSelfAdjoint.posPartRetract [IsTopologicalRing A] [T2Space A] (a : A)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    CFC.posPartRetract a = a⁺ := by
  simp only [CFC.posPartRetract, CFC.abs_add_self a]
  module

end Real

section Isometric

variable [NonUnitalNormedRing A] [StarRing A] [ContinuousStar A]
  [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] [CompleteSpace A]

@[fun_prop]
lemma CFC.continuous_posPartRetract : Continuous (CFC.posPartRetract : A → A) := by
  unfold CFC.posPartRetract; fun_prop

end Isometric

end PosPartRetract
