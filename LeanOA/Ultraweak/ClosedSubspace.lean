module

public import LeanOA.Mathlib.Analysis.Normed.Module.DualQuotient
public import LeanOA.CStarAlgebra.UnitalCorner
public import LeanOA.Ultraweak.Corner

@[expose] public section

/-! # Ultraweakly closed subspaces have preduals

If `N` is an ultraweakly closed subspace of `M`, then `N` is the dual of `P ⧸ N_⊥`, where `N_⊥` is
the subspace of `P` annihilated by `N`. This is Sakai 1.1.4. In particular, if `p` is a projection
in a W⋆-algebra `M`, the corner `p * M * p` (which is a unital C⋆-algebra with unit `p`) is again
a W⋆-algebra.

## Main declarations

+ `Ultraweak.predualOfIsClosed`: the predual of an ultraweakly closed subspace.
+ `IsStarProjection.cornerPredual`: the predual of the corner `p * M * p`.
-/

open scoped Ultraweak
open NonUnitalStarSubalgebra

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
abbrev Subpredual (N : Submodule 𝕜 M) : Type _ := P ⧸ (dualSubmodule P N).preannihilator

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
    ((dualSubmodule P N).equivDualQuotientPreannihilator (isClosed_dualSubmodule hN))

lemma predualOfIsClosed_equivDual_apply_mk (N : Submodule 𝕜 M)
    (hN : IsClosed (ofUltraweak ⁻¹' (N : Set M) : Set (σ(M, P)_𝕜))) (x : N) (ρ : P) :
    (predualOfIsClosed N hN).equivDual x (Submodule.Quotient.mk ρ) =
      Predual.equivDual (𝕜 := 𝕜) (x : M) ρ :=
  Submodule.equivDualQuotientPreannihilator_apply_mk _ (isClosed_dualSubmodule hN) _ ρ

end Subspace

end Ultraweak

namespace IsStarProjection

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

variable (P) in
/-- The corner `p * M * p` of a W⋆-algebra is ultraweakly closed. -/
lemma isClosed_preimage_corner {p : M} (hp : IsStarProjection p) :
    IsClosed (ofUltraweak ⁻¹' (corner ℂ p : Set M) : Set σ(M, P)) :=
  IsStarProjection.isClosed_corner_of_ultraweak (e := toUltraweak ℂ P p) hp

variable (P) in
/-- The predual of the corner `p * M * p` of a W⋆-algebra `M` with predual `P`. Together with
`IsStarProjection.cornerCStarAlgebra`, this makes `p * M * p` into a W⋆-algebra with unit `p`. -/
noncomputable abbrev cornerPredual {p : M} (hp : IsStarProjection p) :
    Predual ℂ (corner ℂ p) (Ultraweak.Subpredual P (corner ℂ p).toSubmodule) :=
  Ultraweak.predualOfIsClosed (corner ℂ p).toSubmodule (hp.isClosed_preimage_corner P)

end IsStarProjection
