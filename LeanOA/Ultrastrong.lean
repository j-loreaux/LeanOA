module

public import LeanOA.Predual
public import LeanOA.Ultraweak.Basic
public import LeanOA.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.TransferInstance

public section

set_option linter.unusedVariables false in
/-- Type synonym for `M` with the ultrastrong topology. -/
@[expose, nolint unusedArguments]
def Ultrastrong (𝕜 M P : Type*) [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P] := M

@[inherit_doc]
scoped[Ultrastrong] notation "s("M", " P")_" 𝕜:max => Ultrastrong 𝕜 M P
@[inherit_doc]
scoped[Ultrastrong] notation "s("M", " P")" => Ultrastrong ℂ M P

/-! ## Linear structure -/

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

open Ultrastrong

variable (𝕜 M P) in
/-- The canonical map from `M` to `s(M, P)_𝕜`. -/
@[expose] def toUltrastrong (x : M) : s(M, P)_𝕜 := x

/-- The canonical map from `s(M, P)_𝕜` to `M`. -/
@[expose] def Ultrastrong.ofUltrastrong (x : s(M, P)_𝕜) : M := x

namespace Ultrastrong

@[simp] lemma toUltrastrong_ofUltrastrong (x : s(M, P)_𝕜) :
    toUltrastrong 𝕜 M P x.ofUltrastrong = x := rfl

@[simp] lemma ofUltrastrong_toUltrastrong (x : M) :
    (toUltrastrong 𝕜 M P x).ofUltrastrong = x := rfl

variable (𝕜 M P) in
/-- The canonical equivalence between `s(M, P)_𝕜` and `M`. -/
@[expose, simps] def equiv : s(M, P)_𝕜 ≃ M where
  toFun := ofUltrastrong
  invFun := toUltrastrong 𝕜 M P

instance : AddCommGroup (s(M, P)_𝕜) := equiv 𝕜 M P |>.addCommGroup
instance : Module 𝕜 (s(M, P)_𝕜) := equiv 𝕜 M P |>.module 𝕜

@[simp] lemma toUltrastrong_add (x y : M) :
    toUltrastrong 𝕜 M P (x + y) = toUltrastrong 𝕜 M P x + toUltrastrong 𝕜 M P y := rfl

@[simp] lemma ofUltrastrong_add (x y : s(M, P)_𝕜) :
    (x + y).ofUltrastrong = x.ofUltrastrong + y.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_smul (a : 𝕜) (x : M) :
    toUltrastrong 𝕜 M P (a • x) = a • toUltrastrong 𝕜 M P x := rfl

@[simp] lemma ofUltrastrong_smul (a : 𝕜) (x : s(M, P)_𝕜) :
    (a • x).ofUltrastrong = a • x.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_zero : toUltrastrong 𝕜 M P (0 : M) = 0 := rfl
@[simp] lemma ofUltrastrong_zero : (0 : s(M, P)_𝕜).ofUltrastrong = 0 := rfl
@[simp] lemma toUltrastrong_neg (x : M) : toUltrastrong 𝕜 M P (-x) = -toUltrastrong 𝕜 M P x := rfl
@[simp] lemma ofUltrastrong_neg (x : s(M, P)_𝕜) : (-x).ofUltrastrong = -x.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_sub (x y : M) :
    toUltrastrong 𝕜 M P (x - y) = toUltrastrong 𝕜 M P x - toUltrastrong 𝕜 M P y := rfl

@[simp] lemma ofUltrastrong_sub (x y : s(M, P)_𝕜) :
    (x - y).ofUltrastrong = x.ofUltrastrong - y.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_inj {x y : M} : toUltrastrong 𝕜 M P x = toUltrastrong 𝕜 M P y ↔ x = y :=
  equiv 𝕜 M P |>.symm.injective.eq_iff

@[simp] lemma ofUltrastrong_inj {x y : s(M, P)_𝕜} : x.ofUltrastrong = y.ofUltrastrong ↔ x = y :=
  equiv 𝕜 M P |>.injective.eq_iff

@[simp] lemma toUltrastrong_eq_zero {x : M} : toUltrastrong 𝕜 M P x = 0 ↔ x = 0 :=
  toUltrastrong_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ toUltrastrong_inj

@[simp] lemma ofUltrastrong_eq_zero {x : s(M, P)_𝕜} : x.ofUltrastrong = 0 ↔ x = 0 :=
  ofUltrastrong_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ ofUltrastrong_inj

/-! ## Equivalences -/

variable (𝕜 M P) in
/-- The canonical linear equivalence between `s(M, P)_𝕜` and `M`. -/
@[expose, simps!]
def linearEquiv : s(M, P)_𝕜 ≃ₗ[𝕜] M where
  toEquiv := equiv 𝕜 M P
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma toEquiv_linearEquiv : (linearEquiv 𝕜 M P).toEquiv = equiv 𝕜 M P := rfl

/-! ## The Topology -/

variable {M P : Type*} [NormedRing M] [PartialOrder M] [StarRing M] [StarOrderedRing M]
variable [NormedAlgebra ℂ M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [StarModule ℂ M] [SelfAdjointDecompose M]

open ComplexOrder PositiveLinearMap

/-- Seminorm family for the ultrastrong topology. -/
@[expose] noncomputable def seminormFamily : SeminormFamily ℂ
    (ι := { f : M →ₚ[ℂ] ℂ // Continuous (f ∘ ofUltraweak (𝕜 := ℂ) (P := P))}) s(M, P) :=
  fun f ↦ (normSeminorm ℂ (f.val.PreGNS')).comp
    ((linearEquiv ℂ M P).trans f.val.toPreGNS').toLinearMap

/-- Filter basis for the seminorm family for the ultrastrong topology. -/
@[expose]
noncomputable def filterBasis : ModuleFilterBasis ℂ s(M, P) := seminormFamily.moduleFilterBasis

noncomputable instance : TopologicalSpace s(M, P) := filterBasis.topology'

/-- This is probably a stupid definition, but in case we want `WithSeminorms`. -/
lemma withSeminorms : WithSeminorms (E := s(M, P)) seminormFamily :=
  { topology_eq_withSeminorms := rfl }

end Ultrastrong
