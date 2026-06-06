module

public import LeanOA.Predual
public import LeanOA.Ultrastrong
public import LeanOA.Ultraweak.Basic
public import LeanOA.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar

public section

set_option linter.unusedVariables false in
/-- Type synonym for `M` with the ultrastrong-⋆ topology.
Notation for this is `s⋆(M, P)_𝕜` or `s⋆(M, P)` when `𝕜 = ℂ` (this is scped to `Ultrastrong`). -/
@[expose, nolint unusedArguments]
def UltrastrongStar (𝕜 M P : Type*) [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P] := M

@[inherit_doc]
scoped[Ultrastrong] notation "s⋆("M", " P")_" 𝕜:max => UltrastrongStar 𝕜 M P
@[inherit_doc]
scoped[Ultrastrong] notation "s⋆("M", " P")" => UltrastrongStar ℂ M P

open scoped Ultrastrong

/-! ## Linear structure -/

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

variable (𝕜 M P) in
/-- The canonical map from `M` to `s⋆(M, P)_𝕜`. -/
@[expose] def toUltrastrongStar (x : M) : s⋆(M, P)_𝕜 := x

/-- The canonical map from `s⋆(M, P)_𝕜` to `M`. -/
@[expose] def UltrastrongStar.ofUltrastrongStar (x : s⋆(M, P)_𝕜) : M := x

namespace UltrastrongStar

@[simp] lemma toUltrastrongStar_ofUltrastrongStar (x : s⋆(M, P)_𝕜) :
    toUltrastrongStar 𝕜 M P x.ofUltrastrongStar = x := rfl

@[simp] lemma ofUltrastrongStar_toUltrastrongStar (x : M) :
    (toUltrastrongStar 𝕜 M P x).ofUltrastrongStar = x := rfl

variable (𝕜 M P) in
/-- The canonical equivalence between `s⋆(M, P)_𝕜` and `M`. -/
@[expose, simps] def equiv : s⋆(M, P)_𝕜 ≃ M where
  toFun := ofUltrastrongStar
  invFun := toUltrastrongStar 𝕜 M P

instance : AddCommGroup (s⋆(M, P)_𝕜) := equiv 𝕜 M P |>.addCommGroup
instance : Module 𝕜 (s⋆(M, P)_𝕜) := equiv 𝕜 M P |>.module 𝕜

@[simp] lemma toUltrastrongStar_add (x y : M) :
    toUltrastrongStar 𝕜 M P (x + y) = toUltrastrongStar 𝕜 M P x + toUltrastrongStar 𝕜 M P y := rfl

@[simp] lemma ofUltrastrongStar_add (x y : s⋆(M, P)_𝕜) :
    (x + y).ofUltrastrongStar = x.ofUltrastrongStar + y.ofUltrastrongStar := rfl

@[simp] lemma toUltrastrongStar_smul (a : 𝕜) (x : M) :
    toUltrastrongStar 𝕜 M P (a • x) = a • toUltrastrongStar 𝕜 M P x := rfl

@[simp] lemma ofUltrastrongStar_smul (a : 𝕜) (x : s⋆(M, P)_𝕜) :
    (a • x).ofUltrastrongStar = a • x.ofUltrastrongStar := rfl

@[simp] lemma toUltrastrongStar_zero : toUltrastrongStar 𝕜 M P (0 : M) = 0 := rfl
@[simp] lemma ofUltrastrongStar_zero : (0 : s⋆(M, P)_𝕜).ofUltrastrongStar = 0 := rfl

@[simp] lemma toUltrastrongStar_neg (x : M) :
  toUltrastrongStar 𝕜 M P (-x) = -toUltrastrongStar 𝕜 M P x := rfl

@[simp] lemma ofUltrastrongStar_neg (x : s⋆(M, P)_𝕜) :
  (-x).ofUltrastrongStar = -x.ofUltrastrongStar := rfl

@[simp] lemma toUltrastrongStar_sub (x y : M) :
    toUltrastrongStar 𝕜 M P (x - y) = toUltrastrongStar 𝕜 M P x - toUltrastrongStar 𝕜 M P y := rfl

@[simp] lemma ofUltrastrongStar_sub (x y : s⋆(M, P)_𝕜) :
    (x - y).ofUltrastrongStar = x.ofUltrastrongStar - y.ofUltrastrongStar := rfl

@[simp] lemma toUltrastrongStar_inj {x y : M} :
    toUltrastrongStar 𝕜 M P x = toUltrastrongStar 𝕜 M P y ↔ x = y :=
  equiv 𝕜 M P |>.symm.injective.eq_iff

@[simp] lemma ofUltrastrongStar_inj {x y : s⋆(M, P)_𝕜} :
    x.ofUltrastrongStar = y.ofUltrastrongStar ↔ x = y :=
  equiv 𝕜 M P |>.injective.eq_iff

@[simp] lemma toUltrastrongStar_eq_zero {x : M} : toUltrastrongStar 𝕜 M P x = 0 ↔ x = 0 :=
  toUltrastrongStar_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ toUltrastrongStar_inj

@[simp] lemma ofUltrastrongStar_eq_zero {x : s⋆(M, P)_𝕜} : x.ofUltrastrongStar = 0 ↔ x = 0 :=
  ofUltrastrongStar_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ ofUltrastrongStar_inj

/-! ## Equivalences -/

variable (𝕜 M P) in
/-- The canonical linear equivalence between `s⋆(M, P)_𝕜` and `M`. -/
@[expose, simps!]
def linearEquiv : s⋆(M, P)_𝕜 ≃ₗ[𝕜] M where
  toEquiv := equiv 𝕜 M P
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ## The Topology -/

variable {M P : Type*} [NormedRing M] [PartialOrder M] [StarRing M] [StarOrderedRing M]
variable [NormedAlgebra ℂ M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [StarModule ℂ M] [SelfAdjointDecompose M]

open ComplexOrder PositiveLinearMap

open Ultraweak in
/-- Seminorm family for the ultrastrong-star topology. -/
@[expose] noncomputable def seminormFamily : SeminormFamily ℂ
    (ι := { f : M →ₚ[ℂ] ℂ // Continuous (f ∘ ofUltraweak (𝕜 := ℂ) (P := P))} × Fin 2)
    s⋆(M, P) :=
  fun f ↦ if f.2 = 0 then normSeminorm ℂ f.1.val.PreGNS' |>.comp
    (linearEquiv ℂ M P |>.trans f.1.val.toPreGNS').toLinearMap else
      normSeminorm ℂ f.1.val.PreGNS' |>.comp <|
        (linearEquiv ℂ M P |>.trans <| f.1.val.toPreGNS').trans
          (starLinearEquiv ℂ (A := M)) |>.toLinearMap

/-- Filter basis for the seminorm family for the ultrastrong-star topology. -/
@[expose]
noncomputable def filterBasis : ModuleFilterBasis ℂ s⋆(M, P) := seminormFamily.moduleFilterBasis

noncomputable instance : TopologicalSpace s⋆(M, P) := filterBasis.topology'

lemma withSeminorms : WithSeminorms (E := s⋆(M, P)) seminormFamily :=
  { topology_eq_withSeminorms := rfl }

/-- Ultrastrong-⋆ topology is stronger than the ultrastrong. -/
lemma continuous_toUltrastrong_ofUltrastrongStar :
    Continuous (fun x : s⋆(M, P) ↦ toUltrastrong ℂ M P x.ofUltrastrongStar) :=
  withSeminorms.continuous_of_isBounded Ultrastrong.withSeminorms
    ((Ultrastrong.linearEquiv ℂ M P).symm.toLinearMap ∘ₗ linearEquiv ℂ M P)
    fun i ↦ ⟨{(i, 0)}, 1, fun _ ↦ by simp [Ultrastrong.seminormFamily, seminormFamily]⟩

end UltrastrongStar
