module

public import LeanOA.Ultraweak.Masa
public import LeanOA.CStarAlgebra.FiniteSpectrum

@[expose] public section

/-! # W⋆-algebras are FS

A W⋆-algebra `M` is FS: its selfadjoint elements are norm limits of selfadjoint elements with
finite spectrum. Indeed, a selfadjoint element lies in a masa, whose character space is
extremally disconnected (Sakai 1.7.5), so that the masa is FS by Sakai 1.3.1
(`ContinuousMap.instFiniteSpectrum`).

Consequently, nonnegative elements of `M` are norm limits of nonnegative combinations of
projections, and the span of the projections is norm dense
(see `CStarAlgebra.FiniteSpectrum.mem_closure_hull_isStarProjection` and
`CStarAlgebra.FiniteSpectrum.topologicalClosure_span_complex_isStarProjection`).
-/

open scoped IsMulCommutative
open WeakDual

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

include P in
/-- A W⋆-algebra is FS. -/
theorem CStarAlgebra.finiteSpectrum_of_predual : CStarAlgebra.FiniteSpectrum M :=
  CStarAlgebra.finiteSpectrum_iff_spectrum.mpr fun x hx ↦ by
    /- Place `x` in a masa `S`, which is FS since its character space is extremally
    disconnected, and approximate `x` within `S`. -/
    have : IsStarNormal x := hx.isStarNormal
    obtain ⟨S, hS, hS_masa⟩ := (StarAlgebra.elemental ℂ x).exists_le_isMasa
    have hxS : x ∈ S := hS (StarAlgebra.elemental.self_mem ℂ x)
    have : ExtremallyDisconnected (characterSpace ℂ S) :=
      StarSubalgebra.IsMasa.extremallyDisconnected_characterSpace (P := P) S
    let _ : CommCStarAlgebra S := IsMulCommutative.instCommCStarAlgebra
    have : CStarAlgebra.FiniteSpectrum S := .of_starAlgEquiv (gelfandStarTransform S)
    have hy : IsSelfAdjoint (⟨x, hxS⟩ : S) := Subtype.ext hx
    have hmap : Set.MapsTo (S.subtype : S → M) {z : S | IsSelfAdjoint z ∧ (spectrum ℝ z).Finite}
        {z : M | IsSelfAdjoint z ∧ (spectrum ℝ z).Finite} := fun z hz ↦
      ⟨hz.1.map S.subtype,
        IsSelfAdjoint.map_spectrum_real hz.1 S.subtype Subtype.val_injective ▸ hz.2⟩
    simpa using map_mem_closure continuous_subtype_val
      (CStarAlgebra.finiteSpectrum_iff_spectrum.mp inferInstance hy) hmap
