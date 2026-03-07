import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

theorem isIdempotentElem_iff_quasispectrum_subset (R : Type*) {A : Type*} {p : A → Prop} [Field R]
    [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a) :
    IsIdempotentElem a ↔ quasispectrum R a ⊆ {0, 1} := by
  refine ⟨IsIdempotentElem.quasispectrum_subset, fun h ↦ ?_⟩
  rw [IsIdempotentElem, ← cfcₙ_id' R a, ← cfcₙ_mul _ _]
  exact cfcₙ_congr fun x hx ↦ by grind

theorem isIdempotentElem_iff_spectrum_subset (R : Type*) {A : Type*} {p : A → Prop} [Field R]
    [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
    [StarRing A] [TopologicalSpace A] [Algebra R A] [NonUnitalContinuousFunctionalCalculus R A p]
    (a : A) (ha : p a) : IsIdempotentElem a ↔ spectrum R a ⊆ {0, 1} := by
  grind [quasispectrum_eq_spectrum_union_zero, isIdempotentElem_iff_quasispectrum_subset R]
