module

public import LeanOA.Mathlib.Analysis.Normed.Module.DualQuotient
public import LeanOA.Ultraweak.Corner

@[expose] public section

/-! # Ultraweakly closed subspaces have preduals

If `N` is an ultraweakly closed subspace of `M`, then `N` is the dual of `P ⧸ N_⊥`, where `N_⊥` is
the subspace of `P` annihilated by `N`. This is Sakai 1.1.4. In particular, if `p` is a projection
in a W⋆-algebra `M`, the corner `hp.Corner` (which is a unital C⋆-algebra with unit `p`) is again
a W⋆-algebra.

## Main declarations

+ `Ultraweak.predualOfIsClosed`: the predual of an ultraweakly closed subspace.
+ `IsStarProjection.Corner.instPredual`: the predual of the corner `hp.Corner`.
-/

open scoped Ultraweak
open Submodule

namespace Ultraweak

section Subspace

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

variable (P) in
/-- The predual `P ⧸ N_⊥` of an ultraweakly closed subspace `N` of `M`. -/
abbrev Subpredual (N : Submodule 𝕜 M) : Type _ :=
  P ⧸ (topDualPairing 𝕜 P).polarSubmodule (map (Predual.equivDual (P := P)).toLinearMap N)

omit [Predual 𝕜 M P] in
lemma ofUltraweak_weakDualCLE_symm_apply [Predual 𝕜 M P] (φ : WeakDual 𝕜 P) :
    ofUltraweak ((weakDualCLE 𝕜 M P).symm φ) = Predual.equivDual.symm (WeakDual.toStrongDual φ) :=
  rfl

lemma isClosed_preimage_map_equivDual {N : Submodule 𝕜 M}
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) :
    IsClosed (WeakDual.toStrongDual ⁻¹' (map (Predual.equivDual (P := P)).toLinearMap N) :
      Set (WeakDual 𝕜 P)) := by
  have : comap WeakDual.toStrongDual.toLinearMap (map Predual.equivDual.toLinearMap N) =
      comap (weakDualCLE 𝕜 M P).symm.toLinearMap
        (comap (Ultraweak.linearEquiv 𝕜 M P).toLinearMap N) := by
    simp only [comap_equiv_eq_map_symm, ← map_comp]
    rfl
  convert hN.preimage (weakDualCLE 𝕜 M P).symm.continuous using 1
  exact congr(SetLike.coe $this)

/-- **Sakai 1.1.4**: an ultraweakly closed subspace `N` of `M` is the dual of `P ⧸ N_⊥`. -/
noncomputable abbrev predualOfIsClosed (N : Submodule 𝕜 M)
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) :
    Predual 𝕜 N (Subpredual P N) where
  equivDual := Predual.equivDual.submoduleMap N |>.trans <|
    (map Predual.equivDual.toLinearMap N).equivDualQuotientPolarSubmodule <| by
      exact isClosed_preimage_map_equivDual hN

lemma predualOfIsClosed_equivDual_apply_mk (N : Submodule 𝕜 M)
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) (x : N) (ρ : P) :
    (predualOfIsClosed N hN).equivDual x (Submodule.Quotient.mk ρ) =
      Predual.equivDual (𝕜 := 𝕜) (x : M) ρ :=
  equivDualQuotientPolarSubmodule_apply_mk _ (isClosed_preimage_map_equivDual hN) _ ρ

end Subspace

end Ultraweak

namespace IsStarProjection

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

variable (P) in
/-- The corner `p * M * p` of a W⋆-algebra is ultraweakly closed. -/
lemma isClosed_preimage_cornerSubmodule {p : M} (hp : IsStarProjection p) :
    IsClosed (ofUltraweak ⁻¹' (hp.cornerSubmodule ℂ : Set M) : Set σ(M, P)) :=
  hp.toUltraweak.isClosed_cornerSubmodule_of_ultraweak

/-- The predual of the corner `hp.Corner` of a W⋆-algebra `M` with predual `P`. Together with
`IsStarProjection.Corner.instCStarAlgebra`, this makes `hp.Corner` into a W⋆-algebra with
unit `p`. -/
noncomputable instance Corner.instPredual {p : M} {hp : IsStarProjection p} :
    Predual ℂ hp.Corner (Ultraweak.Subpredual P (hp.cornerSubmodule ℂ)) where
  equivDual := (hp.cornerLinearIsometryEquiv ℂ).trans
    (Ultraweak.predualOfIsClosed _ (hp.isClosed_preimage_cornerSubmodule P)).equivDual

lemma Corner.predual_equivDual_apply_mk {p : M} {hp : IsStarProjection p} (x : hp.Corner)
    (ρ : P) :
    Predual.equivDual (P := Ultraweak.Subpredual P (hp.cornerSubmodule ℂ)) x
      (Submodule.Quotient.mk ρ) = Predual.equivDual (𝕜 := ℂ) (x : M) ρ :=
  Ultraweak.predualOfIsClosed_equivDual_apply_mk _ (hp.isClosed_preimage_cornerSubmodule P) _ ρ

end IsStarProjection
