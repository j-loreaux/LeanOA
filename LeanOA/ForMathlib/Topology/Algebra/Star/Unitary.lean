import Mathlib.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Star

-- this should probably be a new file so as not to increase the imports of
-- `Topology.Algebra.Star`?

variable {R : Type*} [Monoid R] [StarMul R] [TopologicalSpace R]

instance [ContinuousMul R] : ContinuousMul (unitary R) where
  continuous_mul := continuous_induced_rng.mpr <| by fun_prop

instance [ContinuousStar R] : ContinuousStar (unitary R) where
  continuous_star := continuous_induced_rng.mpr <| by fun_prop

instance [ContinuousStar R] : ContinuousInv (unitary R) where
  continuous_inv := by simp_rw [← unitary.star_eq_inv]; fun_prop

instance [ContinuousMul R] [ContinuousStar R] : IsTopologicalGroup (unitary R) where
