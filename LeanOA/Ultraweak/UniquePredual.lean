module

public import LeanOA.Ultraweak.Sakai

@[expose] public section

/-! # Sakai's theorem and the uniqueness of preduals

Let `M` be a W⋆-algebra. This file proves:

+ **Sakai's theorem** (`Ultraweak.positive_tfae`): for a positive linear functional `φ` on `M` with
  predual `P`, the following are equivalent: `φ` is ultraweakly continuous; `φ` lies in the image of
  `P` in the dual of `M`; `φ` is normal (`ScottContinuous`); `φ` preserves suprema of directed sets
  of projections. In particular, ultraweak continuity of a positive functional depends only on the
  order structure of `M`, not on the predual.
+ **Uniqueness of the ultraweak topology** (`Ultraweak.continuousLinearEquivOfPredual`): for any two
  preduals `P` and `Q` of `M`, the identity map `σ(M, P) → σ(M, Q)` is a homeomorphism.
+ **Uniqueness of the predual** (`Predual.uniqueEquiv`): any two preduals `P` and `Q` of `M` are
  isometrically isomorphic, via an isomorphism compatible with the pairings with `M`.

The proof of uniqueness uses that the ultraweak topology on bounded sets is determined by the
positive ultraweakly continuous functionals (`Ultraweak.continuousOn_of_forall_posCLM`), together
with the Krein–Smulian theorem (`Ultraweak.continuous_of_continuousOn_closedBall`).
-/

open scoped Ultraweak ComplexOrder
open Metric Bornology

namespace Ultraweak

section TFAE

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- **Sakai's theorem**. For a positive linear functional `φ` on a W⋆-algebra `M` with
predual `P`, the following are equivalent:

1. `φ` is ultraweakly continuous;
2. `φ` lies in the image of the predual `P` in the dual of `M`;
3. `φ` is normal, i.e., it preserves suprema of directed sets;
4. `φ` preserves suprema of directed sets of projections. -/
theorem positive_tfae (φ : M →ₚ[ℂ] ℂ) : List.TFAE
    [Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x),
      φ.toContinuousLinearMap ∈ Set.range (Predual.toDual ℂ M P),
      ScottContinuous φ,
      ScottContinuousOn {d : Set M | ∀ q ∈ d, IsStarProjection q} φ] := by
  tfae_have 1 ↔ 2 := continuous_iff_mem_range (P := P) φ.toContinuousLinearMap
  tfae_have 1 → 3 := scottContinuous_of_continuous (P := P) φ
  tfae_have 3 → 4 := ScottContinuous.scottContinuousOn
  tfae_have 4 → 1 := continuous_of_scottContinuousOn (P := P) φ
  tfae_finish

end TFAE

section Unique

variable {M P Q : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

/-- Ultraweak continuity of a positive functional does not depend on the choice of predual. -/
theorem continuous_iff_continuous_of_positive (φ : M →ₚ[ℂ] ℂ) :
    (Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x)) ↔
      Continuous fun x : σ(M, Q) ↦ φ (ofUltraweak x) :=
  ((positive_tfae (P := P) φ).out 1 4).trans ((positive_tfae (P := Q) φ).out 1 4).symm

variable (P Q) in
/-- For any two preduals `P` and `Q` of `M`, the identity map `σ(M, Q) → σ(M, P)` is
continuous. -/
theorem continuous_toUltraweak_ofUltraweak :
    Continuous fun x : σ(M, Q) ↦ toUltraweak ℂ P (ofUltraweak x) := by
  let L : σ(M, Q) →ₗ[ℂ] σ(M, P) :=
    (linearEquiv ℂ M P).symm.toLinearMap ∘ₗ (linearEquiv ℂ M Q).toLinearMap
  /- By Krein–Smulian, it suffices to check continuity on the closed unit ball. There, the
  ultraweak topology is determined by the positive ultraweakly continuous functionals, which are
  the same for `P` and `Q`. -/
  refine continuous_of_continuousOn_closedBall (pairing ℂ M P) L ?_
  refine continuousOn_of_forall_posCLM (P := P) ?_ fun φ ↦ Continuous.continuousOn ?_
  · rw [← isBounded_image_ofUltraweak]
    refine isBounded_closedBall (x := (0 : M)) (r := 1) |>.subset ?_
    rintro - ⟨-, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
  · let ψ : M →ₚ[ℂ] ℂ := (φ.comp (toUltraweakPosCLM P)).toPositiveLinearMap
    exact (continuous_iff_continuous_of_positive (P := P) (Q := Q) ψ).mp (map_continuous φ)

variable (P Q) in
/-- **Uniqueness of the ultraweak topology**: for any two preduals `P` and `Q` of `M`, the identity
of `M` is a homeomorphism `σ(M, P) ≃L[ℂ] σ(M, Q)`. -/
noncomputable def continuousLinearEquivOfPredual : σ(M, P) ≃L[ℂ] σ(M, Q) where
  toLinearEquiv := (linearEquiv ℂ M P).trans (linearEquiv ℂ M Q).symm
  continuous_toFun := continuous_toUltraweak_ofUltraweak Q P
  continuous_invFun := continuous_toUltraweak_ofUltraweak P Q

@[simp]
lemma ofUltraweak_continuousLinearEquivOfPredual (x : σ(M, P)) :
    ofUltraweak (continuousLinearEquivOfPredual P Q x) = ofUltraweak x :=
  rfl

variable (P Q) in
/-- The ultraweakly continuous functionals do not depend on the choice of predual. -/
theorem range_toDual_eq :
    Set.range (Predual.toDual ℂ M P) = Set.range (Predual.toDual ℂ M Q) := by
  ext f
  rw [← continuous_iff_mem_range (P := P), ← continuous_iff_mem_range (P := Q)]
  exact ⟨fun h ↦ h.comp (continuous_toUltraweak_ofUltraweak P Q),
    fun h ↦ h.comp (continuous_toUltraweak_ofUltraweak Q P)⟩

end Unique

end Ultraweak

namespace Predual

open Ultraweak

variable {M P Q : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

variable (M P Q) in
lemma range_toDual_toLinearMap_eq :
    LinearMap.range (toDual ℂ M P).toLinearMap = LinearMap.range (toDual ℂ M Q).toLinearMap :=
  SetLike.coe_injective <| by simpa [LinearMap.coe_range] using range_toDual_eq (M := M) P Q

variable (M P Q) in
/-- The linear isomorphism underlying `Predual.uniqueEquiv`. -/
noncomputable def uniqueEquivₗ : P ≃ₗ[ℂ] Q :=
  LinearEquiv.ofInjective (toDual ℂ M P).toLinearMap (toDual ℂ M P).injective ≪≫ₗ
    LinearEquiv.ofEq _ _ (range_toDual_toLinearMap_eq M P Q) ≪≫ₗ
    (LinearEquiv.ofInjective (toDual ℂ M Q).toLinearMap (toDual ℂ M Q).injective).symm

lemma toDual_uniqueEquivₗ (ρ : P) :
    toDual ℂ M Q (uniqueEquivₗ M P Q ρ) = toDual ℂ M P ρ := by
  let eQ := LinearEquiv.ofInjective (toDual ℂ M Q).toLinearMap (toDual ℂ M Q).injective
  have h := congrArg Subtype.val <| eQ.apply_symm_apply <|
    LinearEquiv.ofEq _ _ (range_toDual_toLinearMap_eq M P Q) <|
      LinearEquiv.ofInjective (toDual ℂ M P).toLinearMap (toDual ℂ M P).injective ρ
  rw [LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply] at h
  exact h

variable (M P Q) in
/-- **Uniqueness of the predual**: any two preduals `P` and `Q` of a W⋆-algebra `M` are
isometrically isomorphic, via an isomorphism compatible with the pairings with `M`
(see `Predual.equivDual_uniqueEquiv_apply`). -/
noncomputable def uniqueEquiv : P ≃ₗᵢ[ℂ] Q where
  toLinearEquiv := uniqueEquivₗ M P Q
  norm_map' ρ := by
    rw [← (toDual ℂ M Q).norm_map, toDual_uniqueEquivₗ, (toDual ℂ M P).norm_map]

/-- The isomorphism `Predual.uniqueEquiv` intertwines the embeddings of the preduals into the
dual of `M`. -/
@[simp]
lemma toDual_uniqueEquiv (ρ : P) : toDual ℂ M Q (uniqueEquiv M P Q ρ) = toDual ℂ M P ρ :=
  toDual_uniqueEquivₗ ρ

/-- The isomorphism `Predual.uniqueEquiv` is compatible with the pairings with `M`. -/
@[simp]
lemma equivDual_uniqueEquiv_apply (m : M) (ρ : P) :
    equivDual (𝕜 := ℂ) m (uniqueEquiv M P Q ρ) = equivDual (𝕜 := ℂ) m ρ :=
  congr($(toDual_uniqueEquiv (M := M) (Q := Q) ρ) m)

end Predual
