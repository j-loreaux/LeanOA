module

public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Algebra.Order.Star.Basic

@[expose] public section

/-! # Approximation by locally constant functions on totally separated spaces

On a compact totally separated space `X`, the locally constant functions are dense in `C(X, ℝ)`
by the Stone–Weierstrass theorem. Consequently, every nonnegative `f : C(X, ℝ)` is a uniform limit
of nonnegative linear combinations of idempotents (i.e., indicator functions of clopen sets).
This is (a slight generalization of) part of Sakai 1.3.1, which is stated for Stonean spaces.
-/

open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [TotallySeparatedSpace X]

namespace ContinuousMap

/-- On a compact totally separated space, the locally constant real functions are dense. -/
lemma topologicalClosure_range_toContinuousMapAlgHom :
    Subalgebra.topologicalClosure
      (LocallyConstant.toContinuousMapAlgHom ℝ : LocallyConstant X ℝ →ₐ[ℝ] C(X, ℝ)).range = ⊤ :=
  subalgebra_topologicalClosure_eq_top_of_separatesPoints _ <|
    LocallyConstant.separatesPoints_range_toContinuousMapAlgHom ℝ

/-- A nonnegative locally constant function on a compact space is a nonnegative linear
combination of idempotents. -/
lemma _root_.LocallyConstant.coe_mem_span_isIdempotentElem {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : LocallyConstant X ℝ) (hf : ∀ x, 0 ≤ f x) :
    (f : C(X, ℝ)) ∈ Submodule.span ℝ≥0 {e : C(X, ℝ) | IsIdempotentElem e} := by
  /- `f` is the sum over its (finite) range of `c • 𝟙_{f ⁻¹' {c}}`. -/
  have hU (c : ℝ) : IsClopen (f ⁻¹' {c}) := f.isLocallyConstant.isClopen_fiber c
  have key : (f : C(X, ℝ)) = ∑ c ∈ f.range_finite.toFinset,
      c.toNNReal • (LocallyConstant.charFn ℝ (hU c) : C(X, ℝ)) := by
    ext x
    rw [ContinuousMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single (f x)]
    · simp [NNReal.smul_def, LocallyConstant.coe_charFn, Real.coe_toNNReal _ (hf x)]
    · intro c _ hc
      simp [NNReal.smul_def, LocallyConstant.coe_charFn, Set.indicator, Ne.symm hc]
    · simp
  rw [key]
  refine Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _ <| Submodule.subset_span ?_
  ext x
  change Set.indicator (f ⁻¹' {c}) (1 : X → ℝ) x * Set.indicator (f ⁻¹' {c}) 1 x =
    Set.indicator (f ⁻¹' {c}) 1 x
  by_cases hx : x ∈ f ⁻¹' {c} <;> simp [hx]

/-- On a compact totally separated space, every nonnegative continuous real function is a
uniform limit of nonnegative linear combinations of idempotents. -/
theorem mem_closure_span_isIdempotentElem_of_nonneg {f : C(X, ℝ)} (hf : 0 ≤ f) :
    f ∈ closure (Submodule.span ℝ≥0 {e : C(X, ℝ) | IsIdempotentElem e} : Set C(X, ℝ)) := by
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  /- Approximate `f` by a locally constant function `g`, and then replace `g` by its positive
  part, which is no further from `f` because `f` is nonnegative. -/
  have hf' : f ∈ closure ((LocallyConstant.toContinuousMapAlgHom ℝ :
      LocallyConstant X ℝ →ₐ[ℝ] C(X, ℝ)).range : Set C(X, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, topologicalClosure_range_toContinuousMapAlgHom]
    trivial
  obtain ⟨-, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.mp hf' ε hε
  let g' : LocallyConstant X ℝ := g.map (max · 0)
  refine ⟨g', LocallyConstant.coe_mem_span_isIdempotentElem g' fun x ↦ le_max_right _ _, ?_⟩
  refine lt_of_le_of_lt ((ContinuousMap.dist_le dist_nonneg).mpr fun x ↦ ?_) hg
  calc dist (f x) (g' x) = |max (f x) 0 - max (g x) 0| := by
        have hfx : 0 ≤ f x := hf x
        simp [g', Real.dist_eq, max_eq_left hfx]
    _ ≤ |f x - g x| := abs_max_sub_max_le_abs _ _ _
    _ = dist (f x) ((LocallyConstant.toContinuousMapAlgHom ℝ g : C(X, ℝ)) x) := by
        simp [Real.dist_eq]
    _ ≤ _ := ContinuousMap.dist_apply_le_dist x

end ContinuousMap
