module

public import LeanOA.Mathlib.Analysis.LocallyConvex.Annihilator
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.Complement

@[expose] public section

/-! # Weak⋆ closed subspaces of a dual space are dual spaces

If `N` is a weak⋆ closed subspace of the dual of a normed space `X`, then `N` is isometrically
isomorphic to the dual of `X ⧸ N.strongDualCoannihilator`, where `N.strongDualCoannihilator` is the
subspace of `X` on which every element of `N` vanishes.

## Main declarations

+ `Submodule.dualQuotientStrongDualCoannihilator`: the isometric embedding of the dual of
  `X ⧸ N.strongDualCoannihilator` into the dual of `X`, given by precomposition with the quotient
  map.
+ `Submodule.equivDualQuotientStrongDualCoannihilator`: if `N` is weak⋆ closed, the isometric
  isomorphism between `N` and the dual of `X ⧸ N.strongDualCoannihilator`.
-/

open scoped NNReal ComplexOrder

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace Submodule

variable (N : Submodule 𝕜 (StrongDual 𝕜 X))

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

/-- The isometric embedding of the dual of `X ⧸ N.strongDualCoannihilator` into the dual of `X`
given by precomposition with the quotient map. -/
noncomputable def dualQuotientStrongDualCoannihilator :
    StrongDual 𝕜 (X ⧸ N.strongDualCoannihilator) →ₗᵢ[𝕜] StrongDual 𝕜 X where
  toFun g := g.comp N.strongDualCoannihilator.mkQL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' g := by
    refine le_antisymm ?_ ?_
    · refine (g.opNorm_comp_le _).trans <| mul_le_of_le_one_right (norm_nonneg _) ?_
      exact (N.strongDualCoannihilator.mkQL : X →L[𝕜] X ⧸ N.strongDualCoannihilator).opNorm_le_bound
        zero_le_one fun x ↦ by
          simpa using Submodule.Quotient.norm_mk_le (S := N.strongDualCoannihilator) x
    · exact g.opNorm_le_bound (norm_nonneg _) <| norm_le_of_forall_mk (norm_nonneg _)
        (g.comp N.strongDualCoannihilator.mkQL).le_opNorm

@[simp]
lemma dualQuotientStrongDualCoannihilator_apply (g : StrongDual 𝕜 (X ⧸ N.strongDualCoannihilator))
    (x : X) :
    N.dualQuotientStrongDualCoannihilator g x = g (Submodule.Quotient.mk x) :=
  rfl

/-- A functional on `X` vanishing on `N.strongDualCoannihilator` factors through the quotient. -/
lemma exists_dualQuotientStrongDualCoannihilator_eq {f : StrongDual 𝕜 X}
    (hf : ∀ x ∈ N.strongDualCoannihilator, f x = 0) :
    ∃ g, N.dualQuotientStrongDualCoannihilator g = f := by
  let g₀ : X ⧸ N.strongDualCoannihilator →ₗ[𝕜] 𝕜 :=
    N.strongDualCoannihilator.liftQ f.toLinearMap fun x hx ↦ hf x hx
  exact ⟨g₀.mkContinuous ‖f‖ (norm_le_of_forall_mk (norm_nonneg f) f.le_opNorm), by ext; rfl⟩

/-- If `N` is a weak⋆ closed subspace of the dual of `X`, then `N` is isometrically isomorphic to
the dual of `X ⧸ N.strongDualCoannihilator`. -/
noncomputable def equivDualQuotientStrongDualCoannihilator
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) :
    N ≃ₗᵢ[𝕜] StrongDual 𝕜 (X ⧸ N.strongDualCoannihilator) :=
  let Ψ : StrongDual 𝕜 (X ⧸ N.strongDualCoannihilator) →ₗᵢ[𝕜] N :=
    { toFun g := ⟨N.dualQuotientStrongDualCoannihilator g,
        (forall_mem_strongDualCoannihilator_apply_eq_zero_iff hN _).mp fun x hx ↦ by
          simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' g := N.dualQuotientStrongDualCoannihilator.norm_map g }
  (LinearIsometryEquiv.ofSurjective Ψ fun f ↦
    have ⟨g, hg⟩ := N.exists_dualQuotientStrongDualCoannihilator_eq (f := f.1)
      fun x hx ↦ (mem_strongDualCoannihilator x).mp hx f.1 f.2
    ⟨g, Subtype.ext hg⟩).symm

lemma dualQuotientStrongDualCoannihilator_equivDualQuotientStrongDualCoannihilator_apply
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) (f : N) :
    N.dualQuotientStrongDualCoannihilator (N.equivDualQuotientStrongDualCoannihilator hN f) = f :=
  congr(Subtype.val $((N.equivDualQuotientStrongDualCoannihilator hN).symm_apply_apply f))

/-- The defining property of `equivDualQuotientStrongDualCoannihilator`. -/
@[simp]
lemma equivDualQuotientStrongDualCoannihilator_apply_mk
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) :
      Set (WeakDual 𝕜 X))) (f : N) (x : X) :
    N.equivDualQuotientStrongDualCoannihilator hN f (Submodule.Quotient.mk x) =
      (f : StrongDual 𝕜 X) x :=
  congr($(N.dualQuotientStrongDualCoannihilator_equivDualQuotientStrongDualCoannihilator_apply
    hN f) x)

end Submodule
