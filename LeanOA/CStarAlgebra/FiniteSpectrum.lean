import LeanOA.ForMathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

-- move to `Mathlib.Topology.MetricSpace.Pseudo.Defs`?
/-- `Pi.single` as a continuous map `C(X, ℝ)`. -/
noncomputable abbrev ContinuousMap.single {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (i : X) : C(X, ℝ) := open Classical in .mk (Pi.single i 1)

@[simp] theorem ContinuousMap.isStarProjection_single {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] (i : X) : IsStarProjection (single i) := by
  simp [isStarProjection_iff, Pi.single_apply, IsIdempotentElem, ContinuousMap.ext_iff,
    IsSelfAdjoint]

@[simp] lemma ContinuousMap.mem_span_isStarProjection_of_finite {X : Type*} [TopologicalSpace X]
    [T1Space X] [Finite X] (f : C(X, ℝ)) :
    f ∈ Submodule.span ℝ {p : C(X, ℝ) | IsStarProjection p} := by
  have := Fintype.ofFinite X
  rw [show f = ∑ i, f i • single i by
    ext x; rw [coe_sum, Finset.sum_apply, Finset.sum_eq_single x] <;> simp_all]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ <| by simp [Submodule.mem_span_of_mem]

variable {A : Type*} [CStarAlgebra A]

/-- A C⋆-algebra is **FS** if the set of self-adjoint elements has a dense subset of
elements with finite spectrum. -/
class CStarAlgebra.FiniteSpectrum (𝕜 A : Type*) [RCLike 𝕜]
    [TopologicalSpace A] [Ring A] [Algebra 𝕜 A] [StarRing A] : Prop where
  fs : {x : A | IsSelfAdjoint x} ⊆ closure {x : A | IsSelfAdjoint x ∧ (spectrum 𝕜 x).Finite}

/-- A self-adjoint element with finite spectrum in a C⋆-algebra is in the span of
star projections. -/
lemma IsSelfAdjoint.mem_span_isStarProjection_of_finite_spectrum {x : A}
    (hx : IsSelfAdjoint x) (h : (spectrum ℝ x).Finite) :
    x ∈ Submodule.span ℝ {p : A | IsStarProjection p} := by
  have : Finite (spectrum ℝ x) := Set.finite_coe_iff.mpr h
  convert (ContinuousMap.id ℝ).restrict (spectrum ℝ x) |>.mem_span_isStarProjection_of_finite
  refine ⟨fun _ ↦ by simp_all, fun h' ↦ Submodule.mem_span.mpr fun p hp ↦ ?_⟩
  have := Submodule.mem_span.mp h' (.comap (cfcHom hx).toLinearMap p)
  simp_all [Set.subset_def, IsStarProjection.map, cfcHom_id]

/-- In a FS C⋆-algebra, the topological closure of the span of star projections is exactly
the submodule of the self adjoint elements. -/
theorem CStarAlgebra.FiniteSpectrum.topologicalClosure_span_isStarProjection
    [h : CStarAlgebra.FiniteSpectrum ℝ A] :
    (Submodule.span ℝ {x : A | IsStarProjection x}).topologicalClosure =
      selfAdjoint.submodule ℝ A := by
  refine le_antisymm (fun x hx ↦ closure_minimal (fun x hx ↦ ?_) ?_ hx) fun x hx ↦ ?_
  · exact Submodule.span_induction (fun _ hx ↦ hx.isSelfAdjoint) (Submodule.zero_mem _)
      (fun _ _ _ _ hx' hy' ↦ Submodule.add_mem _ hx' hy') (by aesop) hx
  · exact isClosed_eq continuous_id'.star continuous_id'
  · exact closure_mono (fun y hy ↦ hy.1.mem_span_isStarProjection_of_finite_spectrum hy.2) (h.fs hx)
