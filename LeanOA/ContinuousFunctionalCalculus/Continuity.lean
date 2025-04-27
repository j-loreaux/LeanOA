import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import LeanOA.ContinuousMap.Uniform

open Filter Topology

section Unital

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

open scoped ContinuousFunctionalCalculus in
theorem continuousAt_cfc [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ := by
  conv =>
    enter [1, x]
    rw [cfc_apply (hf := hf x)]
  apply cfcHom_continuous _ |>.continuousAt.comp
  rwa [ContinuousAt, (hf x₀).tendsto_restrict_iff_tendstoUniformlyOn hf]

open scoped ContinuousFunctionalCalculus in
open UniformOnFun in
theorem continuous_cfc [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  conv =>
    enter [1, x]
    rw [cfc_apply (hf := hf x)]
  apply cfcHom_continuous _ |>.comp
  rwa [ContinuousOn.continuous_restrict_iff_continuous_uniformOnFun hf]

end Unital
