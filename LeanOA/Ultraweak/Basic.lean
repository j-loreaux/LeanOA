import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.WeakDual

/-- A class which encodes a specified isometric linear isomorpism between `M`
and the strong dual of `P`, so that we may treat `P` as a predual of `M`. -/
class Predual (𝕜 M P : Type*) [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] where
  /-- A linear isometric equivalence between `M` and the dual of its predual `P`. -/
  equivDual : M ≃ₗᵢ[𝕜] StrongDual 𝕜 P


set_option linter.unusedVariables false in
/-- A type synonym of `M` equipped with the *ultraweak topology* (also known as the
*σ-weak topology*) relative to a given predual `P`. This is the weak-* topology on
`M` induced by the isometric isomorphism with the dual of `P`. `Ultraweak 𝕜 P M` is
equipped with the scoped notation `σ(M, P)_𝕜`.

The topology is only defined in the presence of a `Predual 𝕜 P M` instance. -/
@[nolint unusedArguments]
abbrev Ultraweak (𝕜 M P : Type*) [RCLike 𝕜] [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] [Predual 𝕜 M P] :=
  WeakBilin <| topDualPairing 𝕜 P ∘ₗ (Predual.equivDual (M := M) |>.toLinearEquiv.toLinearMap)

@[inherit_doc]
scoped[Ultraweak] notation "σ("M ", " P")_" 𝕜:max => Ultraweak 𝕜 M P
@[inherit_doc]
scoped[Ultraweak] notation "σ("M ", " P")" => Ultraweak ℂ M P

/-! ## Linear structure -/

variable {𝕜 M P : Type*}

section Linear

variable [RCLike 𝕜] [NormedAddCommGroup M] [NormedAddCommGroup P]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

open Ultraweak

variable (𝕜 P) in
/-- The canonical map from `M` to `σ(M, P)_𝕜`. -/
def toUltraweak (m : M) : σ(M, P)_𝕜 := m

/-- The canonical map from `σ(M, P)_𝕜` to `M`. -/
def ofUltraweak (m : σ(M, P)_𝕜) : M := m

@[simp]
lemma toUltraweak_ofUltraweak {m : σ(M, P)_𝕜} :
    toUltraweak 𝕜 P (ofUltraweak m) = m := rfl

@[simp]
lemma ofUltraweak_toUltraweak {m : M} :
    ofUltraweak (toUltraweak 𝕜 P m) = m := rfl


@[simp]
lemma ofUltraweak_add (x y : σ(M, P)_𝕜) :
    ofUltraweak (x + y) = ofUltraweak x + ofUltraweak y := rfl

@[simp]
lemma toUltraweak_add (x y : M) :
    toUltraweak 𝕜 P (x + y) = toUltraweak 𝕜 P x + toUltraweak 𝕜 P y := rfl

@[simp]
lemma ofUltraweak_smul {R : Type*} [CommSemiring R] [Module R M]
    (a : R) (x : σ(M, P)_𝕜) : ofUltraweak (a • x) = a • ofUltraweak x := rfl

@[simp]
lemma toUltraweak_smul {R : Type*} [CommSemiring R] [Module R M]
    (a : R) (x : M) : toUltraweak 𝕜 P (a • x) = a • toUltraweak 𝕜 P x := rfl

@[simp]
lemma ofUltraweak_zero : ofUltraweak (0 : σ(M, P)_𝕜) = (0 : M) := rfl

@[simp]
lemma toUltraweak_zero : toUltraweak 𝕜 P (0 : M) = (0 : σ(M, P)_𝕜) := rfl

@[simp]
lemma ofUltraweak_neg (x : σ(M, P)_𝕜) : ofUltraweak (-x) = -ofUltraweak x := rfl

@[simp]
lemma toUltraweak_neg (x : M) : toUltraweak 𝕜 P (-x) = -toUltraweak 𝕜 P x := rfl

@[simp]
lemma ofUltraweak_sub (x y : σ(M, P)_𝕜) :
    ofUltraweak (x - y) = ofUltraweak x - ofUltraweak y := rfl

@[simp]
lemma toUltraweak_sub (x y : M) :
    toUltraweak 𝕜 P (x - y) = toUltraweak 𝕜 P x - toUltraweak 𝕜 P y := rfl

@[simp]
lemma ofUltraweak_eq_zero (x : σ(M, P)_𝕜) : ofUltraweak x = 0 ↔ x = 0 := Iff.rfl

@[simp]
lemma toUltraweak_eq_zero (x : M) : toUltraweak 𝕜 P x = 0 ↔ x = 0 := Iff.rfl

@[simp]
lemma ofUltraweak_inj {x y : σ(M, P)_𝕜} : ofUltraweak x = ofUltraweak y ↔ x = y := Iff.rfl

@[simp]
lemma toUltraweak_inj {x y : M} : toUltraweak 𝕜 P x = toUltraweak 𝕜 P y ↔ x = y := Iff.rfl

/-! ## Equivalences -/

variable (𝕜 M P) in
/-- The canonical linear equivalence between `σ(M, P)_𝕜` and `M`. -/
@[simps]
def Ultraweak.linearEquiv : σ(M, P)_𝕜 ≃ₗ[𝕜] M where
  toFun := ofUltraweak
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := toUltraweak 𝕜 P
  left_inv _ := rfl
  right_inv _ := rfl

lemma Ultraweak.continuous_of_continuous_eval {α : Type*} [TopologicalSpace α] {g : α → σ(M, P)_𝕜}
    (h : ∀ p : P, Continuous fun a ↦ (Predual.equivDual (𝕜 := 𝕜) (ofUltraweak (g a))) p) :
    Continuous g :=
  WeakBilin.continuous_of_continuous_eval _ h

lemma Ultraweak.eval_continuous (p : P) :
    Continuous fun m : σ(M, P)_𝕜 ↦ (Predual.equivDual (𝕜 := 𝕜) (ofUltraweak m)) p :=
  WeakBilin.eval_continuous _ p

lemma toUltraweak_continuous : Continuous <| toUltraweak 𝕜 (M := M) (P := P) :=
  continuous_of_continuous_eval <| Continuous.eval_const
    <| LinearIsometryEquiv.continuous Predual.equivDual

variable (𝕜 M P) in
/-- The canonical continuous linear equivalence between `σ(M, P)_𝕜` and `WeakDual 𝕜 P`. -/
def Ultraweak.weakDualCLE : σ(M, P)_𝕜 ≃L[𝕜] WeakDual 𝕜 P where
  toLinearEquiv :=
    Ultraweak.linearEquiv 𝕜 M P ≪≫ₗ
    Predual.equivDual.toLinearEquiv ≪≫ₗ
    StrongDual.toWeakDual
  continuous_toFun := WeakDual.continuous_of_continuous_eval <| WeakBilin.eval_continuous _
  continuous_invFun := continuous_of_continuous_eval <| by simpa using WeakDual.eval_continuous

-- the notation is still somewhat broken. Maybe we need `σ_𝕜(M, P)`.
instance : T2Space (σ(M, P)_𝕜) := (weakDualCLE 𝕜 M P).symm.toHomeomorph.t2Space
instance [Nontrivial M] : Nontrivial (σ(M, P)_𝕜) := linearEquiv 𝕜 M P |>.nontrivial
instance [Subsingleton M] : Subsingleton (σ(M, P)_𝕜) := linearEquiv 𝕜 M P |>.subsingleton

open WeakDual

variable (𝕜 P)

lemma ofUltraweak_preimage (s : Set M) :
    ofUltraweak ⁻¹' s =
      weakDualCLE 𝕜 M P ⁻¹' (WeakDual.toStrongDual ⁻¹' (Predual.equivDual.symm ⁻¹' s)) := by
  ext; simp [weakDualCLE]

lemma ofUltraweak_preimage_ball (x : M) (r : ℝ) :
    ofUltraweak ⁻¹' (Metric.ball x r) =
      weakDualCLE 𝕜 M P ⁻¹' (WeakDual.toStrongDual ⁻¹' (Metric.ball (Predual.equivDual x) r)) := by
  convert ofUltraweak_preimage ..
  simp

lemma ofUltraweak_preimage_closedBall (x : M) (r : ℝ) :
    ofUltraweak ⁻¹' (Metric.closedBall x r) =
      weakDualCLE 𝕜 M P ⁻¹'
        (WeakDual.toStrongDual ⁻¹'
          (Metric.closedBall (Predual.equivDual x) r)) := by
  convert ofUltraweak_preimage ..
  simp

lemma Ultraweak.isCompact_closedBall (x : M) (r : ℝ) :
    IsCompact (ofUltraweak ⁻¹' (Metric.closedBall x r) : Set (σ(M, P)_𝕜)) := by
  rw [ofUltraweak_preimage_closedBall]
  exact (weakDualCLE 𝕜 M P).toHomeomorph.isCompact_preimage.mpr <|
    WeakDual.isCompact_closedBall ..

lemma Ultraweak.isClosed_closedBall (x : M) (r : ℝ) :
    IsClosed (ofUltraweak ⁻¹' (Metric.closedBall x r) : Set (σ(M, P)_𝕜)) :=
  isCompact_closedBall 𝕜 P x r |>.isClosed

end Linear

namespace Ultraweak

section NonUnitalNormedRing

variable [NonUnitalNormedRing M] [NormedSpace ℂ M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- The nonunital ring structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : NonUnitalRing σ(M, P) := inferInstanceAs (NonUnitalRing M)

@[simp]
lemma ofUltraweak_mul (x y : σ(M, P)) :
    ofUltraweak (x * y) = ofUltraweak x * ofUltraweak y := rfl

@[simp]
lemma toUltraweak_mul (x y : M) :
    toUltraweak ℂ P (x * y) = toUltraweak ℂ P x * toUltraweak ℂ P y := rfl

variable (M P) in
/-- The canonical ring equivalence between `σ(M, P)` and `M`. -/
@[simps]
noncomputable def ofUltraweak_ringEquiv : σ(M, P) ≃+* M where
  toFun := ofUltraweak
  invFun := toUltraweak ℂ P
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end NonUnitalNormedRing

section StarRing

variable [NonUnitalNormedRing M] [NormedSpace ℂ M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [StarRing M]

/-- The StarRing structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : StarRing σ(M, P) := inferInstanceAs (StarRing M)

@[simp]
lemma ofUltraweak_star (x : σ(M, P)) :
    ofUltraweak (star x) = star (ofUltraweak x) := rfl

@[simp]
lemma toUltraweak_star (x : M) :
    toUltraweak ℂ P (star x) = star (toUltraweak ℂ P x) := rfl

variable (M P) in
/-- The canonical StarRing equivalence between `σ(M, P)` and `M`. -/
@[simps]
noncomputable def ofUltraweak_starRingEquiv' : σ(M, P) ≃⋆+* M where
  toFun := ofUltraweak
  invFun := toUltraweak ℂ P
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl

@[simp]
lemma isSelfAdjoint_ofUltraweak {x : σ(M, P)} :
    IsSelfAdjoint (ofUltraweak x) ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff, ← Ultraweak.ofUltraweak_star]

alias ⟨_root_.IsSelfAdjoint.of_ofUltraweak, _root_.IsSelfAdjoint.ofUltraweak⟩
  := isSelfAdjoint_ofUltraweak

@[simp]
lemma isSelfAdjoint_toUltraweak {x : M} :
    IsSelfAdjoint (toUltraweak ℂ P x) ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff, ← Ultraweak.toUltraweak_star]

alias ⟨_root_.IsSelfAdjoint.of_toUltraweak, _root_.IsSelfAdjoint.toUltraweak⟩
  := isSelfAdjoint_toUltraweak

end StarRing

section StarModule

variable [NonUnitalNormedRing M] [NormedSpace ℂ M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [StarRing M] [StarModule ℂ M]

open scoped ComplexStarModule

/-- The star module structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : StarModule ℂ σ(M, P) := inferInstanceAs (StarModule ℂ M)

@[simp]
lemma ofUltraweak_realPart (a : σ(M, P)) :
    ofUltraweak (ℜ a : σ(M, P)) = ℜ (ofUltraweak a) := rfl

@[simp]
lemma toUltraweak_realPart (a : M) :
    toUltraweak ℂ P (ℜ a : M) = ℜ (toUltraweak ℂ P a) := rfl

@[simp]
lemma ofUltraweak_imaginaryPart (a : σ(M, P)) :
    ofUltraweak (ℑ a : σ(M, P)) = ℑ (ofUltraweak a) := rfl

@[simp]
lemma toUltraweak_imaginaryPart (a : M) :
    toUltraweak ℂ P (ℑ a : M) = ℑ (toUltraweak ℂ P a) := rfl

end StarModule

section PartialOrder

variable [NonUnitalNormedRing M] [NormedSpace ℂ M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [PartialOrder M]

/-- The partial order on `σ(M, P)` it inherits from `M`. -/
scoped instance : PartialOrder σ(M, P) :=
  inferInstanceAs (PartialOrder M)


@[simp]
lemma ofUltraweak_nonneg {x : σ(M, P)} :
    0 ≤ ofUltraweak x ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
lemma toUltraweak_nonneg {x : M} :
    0 ≤ toUltraweak ℂ P x ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
lemma ofUltraweak_le {x y : σ(M, P)} :
    ofUltraweak x ≤ ofUltraweak y ↔ x ≤ y :=
  Iff.rfl

@[simp]
lemma toUltraweak_le {x y : M} :
    toUltraweak ℂ P x ≤ toUltraweak ℂ P y ↔ x ≤ y :=
  Iff.rfl

lemma monotone_ofUltraweak :
    Monotone (ofUltraweak : σ(M, P) → M) :=
  fun _ _ ↦ id

lemma monotone_toUltraweak :
    Monotone (toUltraweak ℂ P : M → σ(M, P)) :=
  fun _ _ ↦ id

/-- The identity map from `σ(M, P)` to `M` as an order isomorphism. -/
noncomputable def ofUltraweakOrderIso :
    σ(M, P) ≃o M where
  toFun := ofUltraweak
  invFun := toUltraweak ℂ P
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end PartialOrder

section StarOrderedRing

variable [NonUnitalNormedRing M] [NormedSpace ℂ M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
variable [StarRing M] [PartialOrder M] [StarOrderedRing M]

scoped instance : StarOrderedRing σ(M, P) :=
  inferInstanceAs (StarOrderedRing M)

end StarOrderedRing

section NonUnital

variable [NonUnitalCStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- The NonUnitalCStarAlgebra structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : NonUnitalCStarAlgebra σ(M, P) := inferInstanceAs (NonUnitalCStarAlgebra M)

end NonUnital

/-! ## Ring, star and order structures -/

section Unital

-- With `CStarAlgebra M` and `Predual 𝕜 M P`, this is effectively a `WStarAlgebra M` where
-- we have chosen a particular predual. My feeling is that, when a *statement* involves the
-- predual or ultraweak topology explicitly, then we should use this setup. Later on, when we
-- want to have general results about `WStarAlgebra`s, we can have a `WStarAlgebra.toPredual`
-- `def` which produces a `Predual` instance from a `WStarAlgebra` instance. This will allow us
-- to work with the ultraweak topology in a proof without needing to carry around a predual.
variable [CStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

-- We don't want these intances to pollute `WeakBilin`, so we scope them to `Ultraweak`.
/-- The ring structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : Ring σ(M, P) := inferInstanceAs (Ring M)

/-- The algebra structure on `σ(M, P)` it inherits from `M`. -/
scoped instance : Algebra ℂ σ(M, P) := inferInstanceAs (Algebra ℂ M)

@[simp]
lemma ofUltraweak_one : ofUltraweak (1 : σ(M, P)) = (1 : M) := rfl

@[simp]
lemma toUltraweak_one : toUltraweak ℂ P (1 : M) = (1 : σ(M, P)) := rfl

@[simp]
lemma ofUltraweak_pow (x : σ(M, P)) (n : ℕ) :
    ofUltraweak (x ^ n) = (ofUltraweak x) ^ n := rfl

@[simp]
lemma toUltraweak_pow (x : M) (n : ℕ) :
    toUltraweak ℂ P (x ^ n) = (toUltraweak ℂ P x) ^ n := rfl

@[simp]
lemma ofUltraweak_natCast (n : ℕ) :
    ofUltraweak (n : σ(M, P)) = (n : M) := rfl

@[simp]
lemma toUltraweak_natCast (n : ℕ) :
    toUltraweak ℂ P (n : M) = (n : σ(M, P)) := rfl

@[simp]
lemma ofUltraweak_intCast (n : ℤ) :
    ofUltraweak (n : σ(M, P)) = (n : M) := rfl

@[simp]
lemma toUltraweak_intCast (n : ℤ) :
    toUltraweak ℂ P (n : M) = (n : σ(M, P)) := rfl

@[simp]
lemma ofUltraweak_algebraMap {R : Type*} [CommSemiring R] [Algebra R ℂ] [Algebra R σ(M, P)]
    [IsScalarTower R ℂ σ(M, P)] [Algebra R M] [IsScalarTower R ℂ M] (a : R) :
    ofUltraweak (algebraMap R σ(M, P) a) = algebraMap R M a := by
  rw [IsScalarTower.algebraMap_apply R ℂ, IsScalarTower.algebraMap_apply R ℂ M]
  rfl

@[simp]
lemma toUltraweak_algebraMap {R : Type*} [CommSemiring R] [Algebra R ℂ] [Algebra R σ(M, P)]
    [IsScalarTower R ℂ σ(M, P)] [Algebra R M] [IsScalarTower R ℂ M] (a : R) :
    toUltraweak ℂ P (algebraMap R M a) = algebraMap R σ(M, P) a := by
  rw [IsScalarTower.algebraMap_apply R ℂ, IsScalarTower.algebraMap_apply R ℂ σ(M, P)]
  rfl

variable (M P) in
/-- The canonical algebra equivalence between `σ(M, P)` and `M`. -/
@[simps]
noncomputable def algEquiv : σ(M, P) ≃ₐ[ℂ] M where
  toFun := ofUltraweak
  invFun := toUltraweak ℂ P
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (M P) in
@[simp]
lemma toLinearEquiv_algEquiv : (algEquiv M P).toLinearEquiv = linearEquiv .. := rfl

variable (M P) in
/-- The canonical ⋆-algebra equivalence between `σ(M, P)` and `M`. -/
@[simps!]
noncomputable def starAlgEquiv : σ(M, P) ≃⋆ₐ[ℂ] M := .ofAlgEquiv (algEquiv M P) fun _ ↦ rfl

end Unital

end Ultraweak
