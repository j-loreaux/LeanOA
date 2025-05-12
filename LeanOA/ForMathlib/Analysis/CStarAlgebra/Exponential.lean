import Mathlib.Analysis.CStarAlgebra.Exponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
    [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]

@[simp]
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

attribute [fun_prop] NormedSpace.exp_continuous

@[fun_prop]
lemma selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A → unitary A) := by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  fun_prop
