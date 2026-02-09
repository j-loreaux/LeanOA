import LeanOA.ForMathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.ExtremallyDisconnected

variable {A : Type*} [TopologicalSpace A]

namespace ContinuousMap

-- move to `Mathlib.Topology.MetricSpace.Pseudo.Defs`?
/-- `Pi.single` as a continuous map `C(X, ℝ)`. -/
noncomputable abbrev single [DiscreteTopology A] (i : A) : C(A, ℝ) :=
  open Classical in .mk (Pi.single i 1)

@[simp] theorem isStarProjection_single [DiscreteTopology A] (i : A) :
    IsStarProjection (single i) := by constructor <;> ext <;> simp [Pi.single_apply]

@[simp] lemma mem_span_isStarProjection_of_finite [T1Space A] [Finite A]
    (f : C(A, ℝ)) : f ∈ Submodule.span ℝ {p : C(A, ℝ) | IsStarProjection p} := by
  have := Fintype.ofFinite A
  rw [show f = ∑ i, f i • single i by ext; simp [Finset.sum_pi_single, ← Pi.single_smul]]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ <| by simp [Submodule.mem_span_of_mem]

end ContinuousMap

variable (A) in
/-- A C⋆-algebra is **FS** if the set of self-adjoint elements has a dense subset of
elements with finite spectrum. -/
class CStarAlgebra.FiniteSpectrum [Ring A] [Algebra ℝ A] [StarRing A] : Prop where
  fs : {x : A | IsSelfAdjoint x} ⊆ closure {x : A | IsSelfAdjoint x ∧ (spectrum ℝ x).Finite}

instance [Ring A] [Algebra ℝ A] [StarRing A] [Subsingleton A] : CStarAlgebra.FiniteSpectrum A where
  fs := by nontriviality A; exfalso; exact false_of_nontrivial_of_subsingleton A

section totallySeparatedSpace
variable [TotallySeparatedSpace A]

theorem LocallyConstant.separatesPoints_subalgbraMap_toContinuousMapAlgHom_top (R) [CommSemiring R]
    {Y} [TopologicalSpace Y] [Nontrivial Y] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] :
    (Subalgebra.map (toContinuousMapAlgHom R : _ →ₐ[R] C(A, Y)) ⊤).SeparatesPoints := by
  intro x y hxy
  obtain ⟨U, hU, hxU, hyU : y ∉ U⟩ := exists_isClopen_of_totally_separated hxy
  exact ⟨charFn Y hU, by simp_all [charFn]⟩

open ContinuousMap LocallyConstant in
instance [CompactSpace A] : CStarAlgebra.FiniteSpectrum C(A, ℝ) where
  fs x hx := by
    have : .range toContinuousMap ⊆ {x : C(A, ℝ) | IsSelfAdjoint x ∧ (spectrum ℝ x).Finite} :=
      fun _ ⟨f, hf⟩ ↦ by simp [← hf, spectrum_eq_range, range_finite, IsSelfAdjoint]
    apply closure_mono this
    simpa using Subalgebra.ext_iff.mp (subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (separatesPoints_subalgbraMap_toContinuousMapAlgHom_top ℝ)) x

end totallySeparatedSpace

variable [Ring A] [StarRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

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

/-- In a FS C⋆-algebra, the topological closure of the span of star
projections is exactly the submodule of the self-adjoint elements. -/
@[simp] theorem CStarAlgebra.FiniteSpectrum.topologicalClosure_span_isStarProjection
    [ContinuousConstSMul ℝ A] [ContinuousAdd A] [StarModule ℝ A] [T2Space A]
    [ContinuousStar A] [h : CStarAlgebra.FiniteSpectrum A] :
    (Submodule.span ℝ {x : A | IsStarProjection x}).topologicalClosure =
      selfAdjoint.submodule ℝ A := by
  refine le_antisymm (fun x hx ↦ closure_minimal (fun x hx ↦ ?_) ?_ hx) fun x hx ↦ ?_
  · refine Submodule.span_induction (fun _ hx ↦ hx.isSelfAdjoint) ?_ ?_ ?_ hx <;> aesop
  · exact isClosed_eq continuous_id'.star continuous_id'
  · exact closure_mono (fun y hy ↦ hy.1.mem_span_isStarProjection_of_finite_spectrum hy.2) (h.fs hx)
