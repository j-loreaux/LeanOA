import LeanOA.ForMathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.ExtremallyDisconnected

variable {𝕜 A Y : Type*} [RCLike 𝕜] [TopologicalSpace A] [TopologicalSpace Y]

namespace ContinuousMapZero

/-- A version of `Pi.single` as an element in `C(A, Y)₀` where `single i x 0 = 0`. -/
noncomputable abbrev single [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A] (i : A)
    (x : Y) : C(A, Y)₀ where
  toFun j := if j = 0 then 0 else (Pi.single i x : A → Y) j
  map_zero' := by simp

lemma single_def [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) (j : A) :
    single i x j = if j = 0 then 0 else (Pi.single i x : A → Y) j := rfl

@[simp] lemma sigle_apply_of_ne_zero [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) {j : A} (hj : j ≠ 0) : single i x j = (Pi.single i x : A → Y) j := by simp_all

@[simp] lemma mem_span_isStarProjection_of_finite [DiscreteTopology A] [Finite A] [Zero A]
    (f : C(A, 𝕜)₀) : f ∈ Submodule.span 𝕜 {p : ContinuousMapZero A 𝕜 | IsStarProjection p} := by
  have := Fintype.ofFinite A
  classical
  rw [show f = ∑ i, f i • single i 1 by aesop (add simp [Pi.single_apply])]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ <| Submodule.mem_span_of_mem
    (by constructor <;> ext <;> simp_all [Pi.single_apply, apply_ite])

end ContinuousMapZero

variable (A) in
/-- A C⋆-algebra is **FS (Finite Spectrum)** if the set of self-adjoint elements has a dense subset
of elements with finite spectrum. -/
@[mk_iff]
class CStarAlgebra.FiniteSpectrum [NonUnitalRing A] [Module ℝ A] [Star A] : Prop where
  fs : {x : A | IsSelfAdjoint x} ⊆ closure {x : A | IsSelfAdjoint x ∧ (quasispectrum ℝ x).Finite}

theorem CStarAlgebra.finiteSpectrum_iff_spectrum [Ring A] [Algebra ℝ A] [Star A] :
    CStarAlgebra.FiniteSpectrum A ↔
      {x : A | IsSelfAdjoint x} ⊆ closure {x | IsSelfAdjoint x ∧ (spectrum ℝ x).Finite} := by
  simp [quasispectrum_eq_spectrum_union_zero, CStarAlgebra.finiteSpectrum_iff]

instance [NonUnitalRing A] [Module ℝ A] [StarRing A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Subsingleton A] :
    CStarAlgebra.FiniteSpectrum A where
  fs := by simp [Subsingleton.eq_zero, CFC.quasispectrum_zero_eq]

instance [Ring A] [Algebra ℝ A] [Star A] [Subsingleton A] :
    CStarAlgebra.FiniteSpectrum A where fs := by simp [quasispectrum_eq_spectrum_union_zero]

section totallySeparatedSpace
variable [TotallySeparatedSpace A]

theorem LocallyConstant.separatesPoints_subalgbraMap_toContinuousMapAlgHom_top (R : Type*)
    [CommSemiring R] [Nontrivial Y] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] :
    (Subalgebra.map (toContinuousMapAlgHom R : _ →ₐ[R] C(A, Y)) ⊤).SeparatesPoints := by
  intro x y hxy
  obtain ⟨U, hU, hxU, hyU : y ∉ U⟩ := exists_isClopen_of_totally_separated hxy
  exact ⟨charFn Y hU, by simp_all [charFn]⟩

open ContinuousMap LocallyConstant in
instance [CompactSpace A] : CStarAlgebra.FiniteSpectrum C(A, ℝ) :=
  CStarAlgebra.finiteSpectrum_iff_spectrum.mpr fun x hx ↦ by
    have : .range toContinuousMap ⊆ {x : C(A, ℝ) | IsSelfAdjoint x ∧ (spectrum ℝ x).Finite} :=
      fun _ ⟨f, hf⟩ ↦ by simp [← hf, spectrum_eq_range, range_finite, IsSelfAdjoint]
    apply closure_mono this
    simpa using Subalgebra.ext_iff.mp (subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (separatesPoints_subalgbraMap_toContinuousMapAlgHom_top ℝ)) x

set_option linter.unusedSectionVars false in
proof_wanted CStarAlgebra.finiteSpectrumContinuousMapComplex [CompactSpace A] :
    CStarAlgebra.FiniteSpectrum C(A, ℂ)

end totallySeparatedSpace

variable [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- A self-adjoint element with finite quasispectrum in a non-unital C⋆-algebra is in the span of
star projections. -/
lemma IsSelfAdjoint.mem_span_isStarProjection_of_finite_quasispectrum {x : A}
    (hx : IsSelfAdjoint x) (h : (quasispectrum ℝ x).Finite) :
    x ∈ Submodule.span ℝ {p : A | IsStarProjection p} := by
  have : Finite (quasispectrum ℝ x) := Set.finite_coe_iff.mpr h
  refine Submodule.mem_span.mpr fun p hp ↦ ?_
  simpa [cfcₙHom_id] using Submodule.mem_span.mp
    (ContinuousMapZero.id (quasispectrum ℝ x)).mem_span_isStarProjection_of_finite
    (.comap (cfcₙHom (R := ℝ) hx : _ →ₗ[ℝ] A) p)
    (by simp_all [Set.subset_def, IsStarProjection.map])

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
  · exact closure_mono (fun y hy ↦ hy.1.mem_span_isStarProjection_of_finite_quasispectrum hy.2)
      (h.fs hx)
