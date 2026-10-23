module

public import LeanOA.Ultraweak.Masa
public import LeanOA.Mathlib.Analysis.CStarAlgebra.GelfandDuality

@[expose] public section

/-! # Projections span a dense subspace of a W⋆-algebra

In a W⋆-algebra `M`, every nonnegative element is a norm limit of nonnegative linear combinations
of projections, and consequently the linear span of the projections is norm dense. The former is
obtained by placing the element in a masa, whose character space is extremally disconnected
(Sakai 1.7.5), and applying Sakai 1.3.1 there.
-/

open scoped NNReal IsMulCommutative
open WeakDual

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace WStarAlgebra

include P in
/-- In a W⋆-algebra, every nonnegative element is a norm limit of nonnegative linear combinations
of projections. -/
theorem mem_closure_span_isStarProjection_of_nonneg {a : M} (ha : 0 ≤ a) :
    a ∈ closure (Submodule.span ℝ≥0 {p : M | IsStarProjection p} : Set M) := by
  /- Place `a` in a masa `S`, whose character space is extremally disconnected, and hence
  totally separated. -/
  have : IsStarNormal a := ha.isSelfAdjoint.isStarNormal
  obtain ⟨S, hS, hS_masa⟩ := (StarAlgebra.elemental ℂ a).exists_le_isMasa
  have haS : a ∈ S := hS (StarAlgebra.elemental.self_mem ℂ a)
  have : ExtremallyDisconnected (characterSpace ℂ S) :=
    StarSubalgebra.IsMasa.extremallyDisconnected_characterSpace (P := P) S
  have key := CommCStarAlgebra.mem_closure_span_isStarProjection_of_nonneg
    (A := S) (a := ⟨a, haS⟩) ha
  /- The inclusion of `S` into `M` is continuous and maps projections to projections. -/
  let L : S →ₗ[ℝ≥0] M := S.subtype.toLinearMap.restrictScalars ℝ≥0
  refine map_mem_closure (f := L) continuous_subtype_val key fun x hx ↦ ?_
  refine (Submodule.map_span_le L _ _).mpr (fun y (hy : IsStarProjection y) ↦ ?_) ⟨x, hx, rfl⟩
  exact Submodule.subset_span (show IsStarProjection (y : M) from hy.map S.subtype)

include P in
/-- In a W⋆-algebra, the linear span of the projections is norm dense. -/
theorem topologicalClosure_span_isStarProjection :
    (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure = ⊤ := by
  rw [eq_top_iff, ← CStarAlgebra.span_nonneg, Submodule.span_le]
  intro a (ha : 0 ≤ a)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ (mem_closure_span_isStarProjection_of_nonneg (P := P) ha)
  exact Submodule.span_le_restrictScalars ℝ≥0 ℂ _

end WStarAlgebra
