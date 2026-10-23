module

public import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar
public import LeanOA.AbsConvex
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.Complement

@[expose] public section

/-! # Weak⋆ closed subspaces of a dual space are dual spaces

If `N` is a weak⋆ closed subspace of the dual of a normed space `X`, then `N` is isometrically
isomorphic to the dual of `X ⧸ N.preannihilator`, where `N.preannihilator` is the subspace of `X`
on which every element of `N` vanishes.

## Main declarations

+ `Submodule.preannihilator`: the subspace of `X` annihilated by `N`.
+ `Submodule.dualQuotientPreannihilator`: the isometric embedding of the dual of
  `X ⧸ N.preannihilator` into the dual of `X`, given by precomposition with the quotient map.
+ `Submodule.equivDualQuotientPreannihilator`: if `N` is weak⋆ closed, the isometric isomorphism
  between `N` and the dual of `X ⧸ N.preannihilator`.
-/

open scoped NNReal ComplexOrder

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace Submodule

variable (N : Submodule 𝕜 (StrongDual 𝕜 X))

/-- The *preannihilator* of a subspace `N` of the dual of `X` is the subspace of `X` on which every
element of `N` vanishes. -/
def preannihilator : Submodule 𝕜 X where
  carrier := {x | ∀ f ∈ N, f x = 0}
  add_mem' hx hy f hf := by simp [hx f hf, hy f hf]
  zero_mem' := by simp
  smul_mem' c x hx f hf := by simp [hx f hf]

variable {N} in
lemma mem_preannihilator {x : X} : x ∈ N.preannihilator ↔ ∀ f ∈ N, f x = 0 := Iff.rfl

instance isClosed_preannihilator : IsClosed (N.preannihilator : Set X) := by
  have : (N.preannihilator : Set X) = ⋂ f ∈ N, (f : X → 𝕜) ⁻¹' {0} := by
    ext; simp [mem_preannihilator]
  rw [this]
  exact isClosed_biInter fun f _ ↦ isClosed_singleton.preimage f.continuous

/-- A bound on a function on `X ⧸ S` along the quotient map passes to the quotient norm. -/
private lemma norm_le_of_forall_mk {S : Submodule 𝕜 X} {g : X ⧸ S → 𝕜} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y : X, ‖g (Submodule.Quotient.mk y)‖ ≤ C * ‖y‖) (x : X ⧸ S) : ‖g x‖ ≤ C * ‖x‖ := by
  rcases hC.eq_or_lt with rfl | hC
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S x
    simpa using h y
  · rw [← div_le_iff₀' hC]
    refine QuotientAddGroup.le_norm_iff.mpr fun y hy ↦ (div_le_iff₀' hC).mpr ?_
    rw [← hy]
    exact h y

/-- The isometric embedding of the dual of `X ⧸ N.preannihilator` into the dual of `X` given by
precomposition with the quotient map. -/
noncomputable def dualQuotientPreannihilator :
    StrongDual 𝕜 (X ⧸ N.preannihilator) →ₗᵢ[𝕜] StrongDual 𝕜 X where
  toFun g := g.comp N.preannihilator.mkQL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' g := by
    refine le_antisymm ?_ ?_
    · refine (g.opNorm_comp_le _).trans <| mul_le_of_le_one_right (norm_nonneg _) ?_
      exact (N.preannihilator.mkQL : X →L[𝕜] X ⧸ N.preannihilator).opNorm_le_bound zero_le_one
        fun x ↦ by simpa using Submodule.Quotient.norm_mk_le (S := N.preannihilator) x
    · exact g.opNorm_le_bound (norm_nonneg _) <| norm_le_of_forall_mk (norm_nonneg _)
        (g.comp N.preannihilator.mkQL).le_opNorm

@[simp]
lemma dualQuotientPreannihilator_apply (g : StrongDual 𝕜 (X ⧸ N.preannihilator)) (x : X) :
    N.dualQuotientPreannihilator g x = g (Submodule.Quotient.mk x) :=
  rfl

/-- A functional on `X` vanishing on `N.preannihilator` factors through the quotient. -/
lemma exists_dualQuotientPreannihilator_eq {f : StrongDual 𝕜 X}
    (hf : ∀ x ∈ N.preannihilator, f x = 0) :
    ∃ g, N.dualQuotientPreannihilator g = f := by
  let g₀ : X ⧸ N.preannihilator →ₗ[𝕜] 𝕜 := N.preannihilator.liftQ f.toLinearMap fun x hx ↦ hf x hx
  exact ⟨g₀.mkContinuous ‖f‖ (norm_le_of_forall_mk (norm_nonneg f) f.le_opNorm), by ext; rfl⟩

open WeakDual in
/-- **Bipolar theorem** for weak⋆ closed subspaces: a functional vanishing on the preannihilator of
a weak⋆ closed subspace `N` lies in `N`. -/
lemma mem_of_forall_preannihilator
    (hN : IsClosed (toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) : Set (WeakDual 𝕜 X)))
    {f : StrongDual 𝕜 X} (hf : ∀ x ∈ N.preannihilator, f x = 0) : f ∈ N := by
  let B := weakDualPairing 𝕜 X
  let Nw : Submodule 𝕜 (WeakDual 𝕜 X) := N.comap (toStrongDual (𝕜 := 𝕜) (E := X)).toLinearMap
  have hNw : (Nw : Set (WeakDual 𝕜 X)) = toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) := rfl
  have h_abs : AbsConvex 𝕜 (Nw : Set (WeakDual 𝕜 X)) :=
    ⟨fun a _ ↦ Set.smul_set_subset_iff.mpr fun x hx ↦ Nw.smul_mem a hx, Nw.convex⟩
  have key := B.flip_polar_polar (s := (Nw : Set (WeakDual 𝕜 X))) ⟨0, Nw.zero_mem⟩
  rw [closedAbsConvexHull_eq_self h_abs (hNw ▸ hN), B.polar_subMulAction Nw,
    show {y | ∀ x ∈ Nw, B x y = 0} = (N.preannihilator : Set X) from rfl,
    B.flip.polar_subMulAction N.preannihilator] at key
  have : toStrongDual.symm f ∈ (Nw : Set (WeakDual 𝕜 X)) := key ▸ fun x hx ↦ hf x hx
  simpa [Nw] using this

/-- If `N` is a weak⋆ closed subspace of the dual of `X`, then `N` is isometrically isomorphic to
the dual of `X ⧸ N.preannihilator`. -/
noncomputable def equivDualQuotientPreannihilator
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) :
    N ≃ₗᵢ[𝕜] StrongDual 𝕜 (X ⧸ N.preannihilator) :=
  let Ψ : StrongDual 𝕜 (X ⧸ N.preannihilator) →ₗᵢ[𝕜] N :=
    { toFun g := ⟨N.dualQuotientPreannihilator g, N.mem_of_forall_preannihilator hN fun x hx ↦ by
        simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' g := N.dualQuotientPreannihilator.norm_map g }
  (LinearIsometryEquiv.ofSurjective Ψ fun f ↦
    have ⟨g, hg⟩ := N.exists_dualQuotientPreannihilator_eq (f := f.1) (fun x hx ↦ hx f.1 f.2)
    ⟨g, Subtype.ext hg⟩).symm

lemma dualQuotientPreannihilator_equivDualQuotientPreannihilator_apply
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) (f : N) :
    N.dualQuotientPreannihilator (N.equivDualQuotientPreannihilator hN f) = f :=
  congr(Subtype.val $((N.equivDualQuotientPreannihilator hN).symm_apply_apply f))

/-- The defining property of `equivDualQuotientPreannihilator`. -/
@[simp]
lemma equivDualQuotientPreannihilator_apply_mk
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) (f : N) (x : X) :
    N.equivDualQuotientPreannihilator hN f (Submodule.Quotient.mk x) = (f : StrongDual 𝕜 X) x :=
  congr($(N.dualQuotientPreannihilator_equivDualQuotientPreannihilator_apply hN f) x)

end Submodule
