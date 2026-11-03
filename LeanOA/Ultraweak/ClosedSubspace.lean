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

namespace Ultraweak

section Subspace

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

variable (P) in
/-- The image of a subspace of `M` in the dual of the predual `P`. -/
noncomputable abbrev dualSubmodule (N : Submodule 𝕜 M) : Submodule 𝕜 (StrongDual 𝕜 P) :=
  N.map (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) : M →ₗ[𝕜] StrongDual 𝕜 P)

variable (P) in
/-- The predual `P ⧸ N_⊥` of an ultraweakly closed subspace `N` of `M`. -/
abbrev Subpredual (N : Submodule 𝕜 M) : Type _ :=
  P ⧸ (topDualPairing 𝕜 P).polarSubmodule (dualSubmodule P N)

omit [Predual 𝕜 M P] in
lemma ofUltraweak_weakDualCLE_symm_apply [Predual 𝕜 M P] (φ : WeakDual 𝕜 P) :
    ofUltraweak ((weakDualCLE 𝕜 M P).symm φ) =
      (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).symm (WeakDual.toStrongDual φ) :=
  rfl

lemma isClosed_dualSubmodule {N : Submodule 𝕜 M}
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) :
    IsClosed (WeakDual.toStrongDual ⁻¹' (dualSubmodule P N : Set (StrongDual 𝕜 P)) :
      Set (WeakDual 𝕜 P)) := by
  have : WeakDual.toStrongDual ⁻¹' (dualSubmodule P N : Set (StrongDual 𝕜 P)) =
      (weakDualCLE 𝕜 M P).symm ⁻¹' (ofUltraweak ⁻¹' (N : Set M)) := by
    ext φ
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_map]
    constructor
    · rintro ⟨m, hm, hφ⟩
      rw [ofUltraweak_weakDualCLE_symm_apply, ← hφ]
      simpa using hm
    · intro h
      exact ⟨_, h, by rw [ofUltraweak_weakDualCLE_symm_apply]; simp⟩
  rw [this]
  exact hN.preimage (weakDualCLE 𝕜 M P).symm.continuous

/-- **Sakai 1.1.4**: an ultraweakly closed subspace `N` of `M` is the dual of `P ⧸ N_⊥`. -/
noncomputable abbrev predualOfIsClosed (N : Submodule 𝕜 M)
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) :
    Predual 𝕜 N (Subpredual P N) where
  equivDual := (LinearIsometryEquiv.submoduleMap N Predual.equivDual).trans
    ((dualSubmodule P N).equivDualQuotientPolarSubmodule (isClosed_dualSubmodule hN))

lemma predualOfIsClosed_equivDual_apply_mk (N : Submodule 𝕜 M)
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) (x : N) (ρ : P) :
    (predualOfIsClosed N hN).equivDual x (Submodule.Quotient.mk ρ) =
      Predual.equivDual (𝕜 := 𝕜) (x : M) ρ :=
  Submodule.equivDualQuotientPolarSubmodule_apply_mk _ (isClosed_dualSubmodule hN) _ ρ

end Subspace

end Ultraweak

namespace IsStarProjection

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

variable (P) in
/-- The corner `p * M * p` of a W⋆-algebra is ultraweakly closed. -/
lemma isClosed_preimage_cornerSubmodule {p : M} (hp : IsStarProjection p) :
    IsClosed (ofUltraweak ⁻¹' (hp.cornerSubmodule ℂ : Set M) : Set σ(M, P)) :=
  IsStarProjection.isClosed_cornerSubmodule_of_ultraweak (e := toUltraweak ℂ P p) hp

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
