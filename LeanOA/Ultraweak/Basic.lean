import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.WeakDual

-- So, if we make `P` an `outParam`, then we can only ever use one predual,
-- but the advantage is that we don't have to mention `P` anywhere. I'm not
-- sure what the best approach is.
/-- A class which encodes a specified isometric linear isomorpism between `M`
and the strong dual of `P`, so that we may treat `P` as a predual of `M`. -/
class Predual (𝕜 P M : Type*) [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] where
  /-- A linear isometric equivalence between `M` and the dual of its predual `P`. -/
  equivDual : M ≃ₗᵢ[𝕜] StrongDual 𝕜 P


set_option linter.unusedVariables false in
/-- A type synonym of `M` equipped with the *ultraweak topology* (also known as the
*σ-weak topology*) relative to a given predual `P`. This is the weak-* topology on
`M` induced by the isometric isomorphism with the dual of `P`. `Ultraweak 𝕜 P M` is
equipped with the scoped notation `σ(P, M)_𝕜`.

The topology is only defined in the presence of a `Predual 𝕜 P M` instance. -/
@[nolint unusedArguments]
abbrev Ultraweak (𝕜 P M : Type*) [RCLike 𝕜] [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] [Predual 𝕜 P M] :=
  WeakBilin <| topDualPairing 𝕜 P ∘ₗ (Predual.equivDual (M := M) |>.toLinearEquiv.toLinearMap)

@[inherit_doc]
scoped[Ultraweak] notation "σ("P ", " M")_" 𝕜 => Ultraweak 𝕜 P M
scoped[Ultraweak] notation "σ("P ", " M")" => Ultraweak ℂ P M
-- σ(P, M)_𝕜
-- sometimes we have to write `(σ(P, M)_𝕜)` so that this doesn't use the `FunLike` instance on
-- `WeakBilin`. Gross. Should we make this a `def`? We're going to need to transport ring
-- instances over to this type anyway. And those would infect `WeakBilin` unless we made it a `def`.
-- We can use `scoped` instances for the ring structure to avoid this pollution.

/-! ## Linear structure -/

variable {𝕜 P M : Type*}

section Linear

variable [RCLike 𝕜] [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] [Predual 𝕜 P M]

open Ultraweak

variable (𝕜 P) in
/-- The canonical map from `M` to `σ(P, M)_𝕜`. -/
def toUltraweak (m : M) : σ(P, M)_𝕜 := m

/-- The canonical map from `σ(P, M)_𝕜` to `M`. -/
def ofUltraweak (m : σ(P, M)_𝕜) : M := m

@[simp]
lemma toUltraweak_ofUltraweak {m : σ(P, M)_𝕜} :
    toUltraweak 𝕜 P (ofUltraweak m) = m := rfl

@[simp]
lemma ofUltraweak_toUltraweak {m : M} :
    ofUltraweak (toUltraweak 𝕜 P m) = m := rfl


@[simp]
lemma ofUltraweak_add (x y : σ(P, M)_𝕜) :
    ofUltraweak (x + y) = ofUltraweak x + ofUltraweak y := rfl

@[simp]
lemma toUltraweak_add (x y : M) :
    toUltraweak 𝕜 P (x + y) = toUltraweak 𝕜 P x + toUltraweak 𝕜 P y := rfl

-- probably we should generalize the `𝕜` here to a more general `SMul` so it will handle
-- `ℕ` and `ℤ` too.
@[simp]
lemma ofUltraweak_smul (a : 𝕜) (x : σ(P, M)_𝕜) : ofUltraweak (a • x) = a • ofUltraweak x := rfl

-- probably we should generalize the `𝕜` here to a more general `SMul` so it will handle
-- `ℕ` and `ℤ` too.
@[simp]
lemma toUltraweak_smul (a : 𝕜) (x : M) : toUltraweak 𝕜 P (a • x) = a • toUltraweak 𝕜 P x := rfl

@[simp]
lemma ofUltraweak_zero : ofUltraweak (0 : σ(P, M)_𝕜) = (0 : M) := rfl

@[simp]
lemma toUltraweak_zero : toUltraweak 𝕜 P (0 : M) = (0 : σ(P, M)_𝕜) := rfl

@[simp]
lemma ofUltraweak_neg (x : σ(P, M)_𝕜) : ofUltraweak (-x) = -ofUltraweak x := rfl

@[simp]
lemma toUltraweak_neg (x : M) : toUltraweak 𝕜 P (-x) = -toUltraweak 𝕜 P x := rfl

@[simp]
lemma ofUltraweak_sub (x y : σ(P, M)_𝕜) :
    ofUltraweak (x - y) = ofUltraweak x - ofUltraweak y := rfl

@[simp]
lemma toUltraweak_sub (x y : M) :
    toUltraweak 𝕜 P (x - y) = toUltraweak 𝕜 P x - toUltraweak 𝕜 P y := rfl

@[simp]
lemma ofUltraweak_eq_zero (x : σ(P, M)_𝕜) : ofUltraweak x = 0 ↔ x = 0 := Iff.rfl

@[simp]
lemma toUltraweak_eq_zero (x : M) : toUltraweak 𝕜 P x = 0 ↔ x = 0 := Iff.rfl

@[simp]
lemma ofUltraweak_inj {x y : σ(P, M)_𝕜} : ofUltraweak x = ofUltraweak y ↔ x = y := Iff.rfl

@[simp]
lemma toUltraweak_inj {x y : M} : toUltraweak 𝕜 P x = toUltraweak 𝕜 P y ↔ x = y := Iff.rfl

/-! ## Equivalences -/

/-- The canonical linear equivalence between `σ(P, M)_𝕜` and `M`. -/
@[simps]
def Ultraweak.linearEquiv : (σ(P, M)_𝕜) ≃ₗ[𝕜] M where
  toFun := ofUltraweak
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := toUltraweak 𝕜 P
  left_inv _ := rfl
  right_inv _ := rfl

lemma Ultraweak.continuous_of_continuous_eval {α : Type*} [TopologicalSpace α] {g : α → σ(P, M)_𝕜}
    (h : ∀ p : P, Continuous fun a ↦ (Predual.equivDual (𝕜 := 𝕜) (ofUltraweak (g a))) p) :
    Continuous g :=
  WeakBilin.continuous_of_continuous_eval _ h

lemma Ultraweak.eval_continuous (p : P) :
    Continuous fun m : σ(P, M)_𝕜 ↦ (Predual.equivDual (𝕜 := 𝕜) (ofUltraweak m)) p :=
  WeakBilin.eval_continuous _ p

/-- The canonical continuous linear equivalence between `σ(P, M)_𝕜` and `WeakDual 𝕜 P`. -/
def Ultraweak.weakDualCLE : (σ(P, M)_𝕜) ≃L[𝕜] WeakDual 𝕜 P where
  toLinearEquiv :=
    Ultraweak.linearEquiv ≪≫ₗ
    Predual.equivDual.toLinearEquiv ≪≫ₗ
    StrongDual.toWeakDual
  continuous_toFun := WeakDual.continuous_of_continuous_eval <| WeakBilin.eval_continuous _
  continuous_invFun := continuous_of_continuous_eval <| by simpa using WeakDual.eval_continuous

end Linear

namespace Ultraweak

/-! ## Ring, star and order structures -/

-- With `CStarAlgebra M` and `Predual 𝕜 P M`, this is effectively a `WStarAlgebra M` where
-- we have chosen a particular predual. My feeling is that, when a *statement* involves the
-- predual or ultraweak topology explicitly, then we should use this setup. Later on, when we
-- want to have general results about `WStarAlgebra`s, we can have a `WStarAlgebra.toPredual`
-- `def` which produces a `Predual` instance from a `WStarAlgebra` instance. This will allow us
-- to work with the ultraweak topology in a proof without needing to carry around a predual.
variable [CStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ P M]

-- We don't want these intances to pollute `WeakBilin`, so we scope them to `Ultraweak`.
/-- The ring structure on `σ(P, M)` it inherits from `M`. -/
scoped instance : Ring (σ(P, M)) := inferInstanceAs (Ring M)
/-- The algebra structure on `σ(P, M)` it inherits from `M`. -/
scoped instance : Algebra ℂ (σ(P, M)) := inferInstanceAs (Algebra ℂ M)

@[simp]
lemma ofUltraweak_one : ofUltraweak (1 : σ(P, M)) = (1 : M) := rfl

@[simp]
lemma toUltraweak_one : toUltraweak ℂ P (1 : M) = (1 : σ(P, M)) := rfl

@[simp]
lemma ofUltraweak_mul (x y : σ(P, M)) :
    ofUltraweak (x * y) = ofUltraweak x * ofUltraweak y := rfl

@[simp]
lemma toUltraweak_mul (x y : M) :
    toUltraweak ℂ P (x * y) = toUltraweak ℂ P x * toUltraweak ℂ P y := rfl

@[simp]
lemma ofUltraweak_pow (x : σ(P, M)) (n : ℕ) :
    ofUltraweak (x ^ n) = (ofUltraweak x) ^ n := rfl

@[simp]
lemma toUltraweak_pow (x : M) (n : ℕ) :
    toUltraweak ℂ P (x ^ n) = (toUltraweak ℂ P x) ^ n := rfl

@[simp]
lemma ofUltraweak_natCast (n : ℕ) :
    ofUltraweak (n : σ(P, M)) = (n : M) := rfl

@[simp]
lemma toUltraweak_natCast (n : ℕ) :
    toUltraweak ℂ P (n : M) = (n : σ(P, M)) := rfl

@[simp]
lemma ofUltraweak_intCast (n : ℤ) :
    ofUltraweak (n : σ(P, M)) = (n : M) := rfl

@[simp]
lemma toUltraweak_intCast (n : ℤ) :
    toUltraweak ℂ P (n : M) = (n : σ(P, M)) := rfl

@[simp]
lemma ofUltraweak_algebraMap (a : ℂ) :
    ofUltraweak (algebraMap ℂ (σ(P, M)) a) = algebraMap ℂ M a := rfl

@[simp]
lemma toUltraweak_algebraMap (a : ℂ) :
    toUltraweak ℂ P (algebraMap ℂ M a) = algebraMap ℂ (σ(P, M)) a := rfl

/-- The canonical algebra equivalence between `σ(P, M)_ℂ` and `M`. -/
@[simps]
noncomputable def algEquiv : (σ(P, M)_ℂ) ≃ₐ[ℂ] M where
  toFun := ofUltraweak
  invFun := toUltraweak ℂ P
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma toLinearEquiv_algEquiv :
    algEquiv.toLinearEquiv = linearEquiv (𝕜 := ℂ) (P := P) (M := M) := rfl

/-- The star ring structure on `σ(P, M)` it inherits from `M`. -/
scoped instance : StarRing (σ(P, M)) := inferInstanceAs (StarRing M)
/-- The partial order on `σ(P, M)` it inherits from `M`. -/
scoped instance [PartialOrder M] : PartialOrder (σ(P, M)) :=
  inferInstanceAs (PartialOrder M)
scoped instance [PartialOrder M] [StarOrderedRing M] : StarOrderedRing (σ(P, M)) :=
  inferInstanceAs (StarOrderedRing M)

/-- The canonical ⋆-algebra equivalence between `σ(P, M)_ℂ` and `M`. -/
@[simps!]
noncomputable def starAlgEquiv : (σ(P, M)_ℂ) ≃⋆ₐ[ℂ] M := .ofAlgEquiv algEquiv fun _ ↦ rfl

end Ultraweak
