module

public import LeanOA.Mathlib.Analysis.LocallyConvex.PolarSubmodule
public import LeanOA.Mathlib.Analysis.Normed.Operator.Quotient
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Algebra.Module.Complement

@[expose] public section

/-! # Weak⋆ closed subspaces of a dual space are dual spaces

If `N` is a weak⋆ closed subspace of the dual of a normed space `X`, then `N` is isometrically
isomorphic to the dual of `X ⧸ (topDualPairing 𝕜 X).polarSubmodule N`, where
`(topDualPairing 𝕜 X).polarSubmodule N` is the subspace of `X` on which every element of `N`
vanishes.

## Main declarations

+ `Submodule.dualQuotientPolarSubmodule`: the isometric embedding of the dual of
  `X ⧸ (topDualPairing 𝕜 X).polarSubmodule N` into the dual of `X`, given by precomposition with
  the quotient map.
+ `Submodule.equivDualQuotientPolarSubmodule`: if `N` is weak⋆ closed, the isometric isomorphism
  between `N` and the dual of `X ⧸ (topDualPairing 𝕜 X).polarSubmodule N`.
-/

open scoped NNReal ComplexOrder

open Submodule

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace Submodule

variable (N : Submodule 𝕜 (StrongDual 𝕜 X))

/-- If `N` is weak⋆ closed, then a functional vanishing on `(topDualPairing 𝕜 X).polarSubmodule N`
lies in `N`. -/
lemma forall_mem_topDualPairing_polarSubmodule_apply_eq_zero_iff
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) : Set (WeakDual 𝕜 X)))
    (φ : StrongDual 𝕜 X) :
    (∀ x ∈ (topDualPairing 𝕜 X).polarSubmodule N, φ x = 0) ↔ φ ∈ N := by
  let N' := comap (WeakDual.toStrongDual (𝕜 := 𝕜) (E := X)).toLinearMap N
  have hN' : IsClosed (N' : Set (WeakDual 𝕜 X)) := hN
  convert! LinearMap.IsWeak.forall_mem_polarSubmodule_apply_eq_zero_iff (weakDualPairing 𝕜 X) N'
    (StrongDual.toWeakDual φ) using 1
  rw [hN'.submodule_topologicalClosure_eq]
  rfl

/-- The isometric embedding of the dual of `X ⧸ (topDualPairing 𝕜 X).polarSubmodule N` into the
dual of `X` given by precomposition with the quotient map. -/
noncomputable def dualQuotientPolarSubmodule :
    StrongDual 𝕜 (X ⧸ (topDualPairing 𝕜 X).polarSubmodule N) →ₗᵢ[𝕜] StrongDual 𝕜 X where
  toFun g := g.comp ((topDualPairing 𝕜 X).polarSubmodule N).mkQL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := ContinuousLinearMap.opNorm_comp_mkQL

@[simp]
lemma dualQuotientPolarSubmodule_apply
    (g : StrongDual 𝕜 (X ⧸ (topDualPairing 𝕜 X).polarSubmodule N)) (x : X) :
    N.dualQuotientPolarSubmodule g x = g (Submodule.Quotient.mk x) :=
  rfl

/-- A functional on `X` vanishing on `(topDualPairing 𝕜 X).polarSubmodule N` factors through the
quotient. -/
lemma exists_dualQuotientPolarSubmodule_eq {f : StrongDual 𝕜 X}
    (hf : ∀ x ∈ (topDualPairing 𝕜 X).polarSubmodule N, f x = 0) :
    ∃ g, N.dualQuotientPolarSubmodule g = f :=
  ⟨((topDualPairing 𝕜 X).polarSubmodule N).liftQL f hf, rfl⟩

/-- If `N` is a weak⋆ closed subspace of the dual of `X`, then `N` is isometrically isomorphic to
the dual of `X ⧸ (topDualPairing 𝕜 X).polarSubmodule N`. -/
noncomputable def equivDualQuotientPolarSubmodule
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) : Set (WeakDual 𝕜 X))) :
    N ≃ₗᵢ[𝕜] StrongDual 𝕜 (X ⧸ (topDualPairing 𝕜 X).polarSubmodule N) :=
  let Ψ : StrongDual 𝕜 (X ⧸ (topDualPairing 𝕜 X).polarSubmodule N) →ₗᵢ[𝕜] N :=
    { toFun g := ⟨N.dualQuotientPolarSubmodule g,
        (N.forall_mem_topDualPairing_polarSubmodule_apply_eq_zero_iff hN _).mp fun x hx ↦ by
          simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' g := N.dualQuotientPolarSubmodule.norm_map g }
  (LinearIsometryEquiv.ofSurjective Ψ fun f ↦
    have ⟨g, hg⟩ := N.exists_dualQuotientPolarSubmodule_eq (f := f.1)
      fun x hx ↦ by simpa using (LinearMap.mem_polarSubmodule _).mp hx f.1 f.2
    ⟨g, Subtype.ext hg⟩).symm

lemma dualQuotientPolarSubmodule_equivDualQuotientPolarSubmodule_apply
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) : Set (WeakDual 𝕜 X)))
    (f : N) :
    N.dualQuotientPolarSubmodule (N.equivDualQuotientPolarSubmodule hN f) = f :=
  congr(Subtype.val $((N.equivDualQuotientPolarSubmodule hN).symm_apply_apply f))

/-- The defining property of `equivDualQuotientPolarSubmodule`. -/
@[simp]
lemma equivDualQuotientPolarSubmodule_apply_mk
    (hN : IsClosed (WeakDual.toStrongDual ⁻¹' (N : Set (StrongDual 𝕜 X)) : Set (WeakDual 𝕜 X)))
    (f : N) (x : X) :
    N.equivDualQuotientPolarSubmodule hN f (Submodule.Quotient.mk x) = (f : StrongDual 𝕜 X) x :=
  congr($(N.dualQuotientPolarSubmodule_equivDualQuotientPolarSubmodule_apply hN f) x)

end Submodule
