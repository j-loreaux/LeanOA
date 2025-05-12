import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.ContinuousMap.ContinuousSqrt

variable {A : Type*} [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
variable [PartialOrder A] [StarOrderedRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]


lemma CFC.sqrt_eq_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  suffices cfcₙ (fun x : ℝ ↦ √x * √x) a = cfcₙ (fun x : ℝ ↦ x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ ↦ Real.sqrt_nonneg x))] at this
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx
