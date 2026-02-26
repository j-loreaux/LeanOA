import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Complex.Basic
import LeanOA.Mathlib.Algebra.Order.Module.PositiveLinearMap


namespace PositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommGroup E₁] [PartialOrder E₁]
    [NonUnitalRing E₂] [PartialOrder E₂]
    [Star E₁] [StarRing E₂] [StarOrderedRing E₂]
    [Module R E₁] [Module R E₂] [SelfAdjointDecompose E₁]

lemma map_isSelfAdjoint (f : E₁ →ₚ[R] E₂) {a : E₁} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (f a) := by
  obtain ⟨b, c, hb, hc, rfl⟩ := ha.exists_nonneg_sub_nonpos
  cfc_tac

section StarHomClass
open ComplexStarModule

variable {A₁ A₂ : Type*} [AddCommGroup A₁] [Module ℂ A₁]
    [PartialOrder A₁] [StarAddMonoid A₁] [SelfAdjointDecompose A₁]
    [NonUnitalRing A₂] [Module ℂ A₂]
    [StarRing A₂] [PartialOrder A₂] [StarOrderedRing A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]

instance : StarHomClass (A₁ →ₚ[ℂ] A₂) A₁ A₂ where
  map_star φ x := by
    rw [← realPart_add_I_smul_imaginaryPart x]
    simp [φ.map_isSelfAdjoint (ℜ x).2, IsSelfAdjoint.star_eq,
      φ.map_isSelfAdjoint (ℑ x).2]

set_option backward.isDefEq.respectTransparency false in
lemma map_realPart (φ : A₁ →ₚ[ℂ] A₂) (x : A₁) :
    φ (ℜ x) = ℜ (φ x) := by
  simp [realPart_apply_coe, map_star]

set_option backward.isDefEq.respectTransparency false in
lemma map_imaginaryPart (φ : A₁ →ₚ[ℂ] A₂) (x : A₁) :
    φ (ℑ x) = ℑ (φ x) := by
  simp [imaginaryPart_apply_coe, map_star]

end StarHomClass

end PositiveLinearMap

/-- A `PositiveContinuousLinearMap` is a linear map which is both
positive and continuous. This comes equipped with the notation
`E₁ →P[R] E₂`. -/
structure PositiveContinuousLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [TopologicalSpace E₁]
    [AddCommMonoid E₂] [PartialOrder E₂] [TopologicalSpace E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₚ[R] E₂, E₁ →L[R] E₂

/-- Notation for a `PositiveContinuousLinearMap`. -/
notation:25 E " →P[" R:25 "] " F:0 => PositiveContinuousLinearMap R E F

/-- The `ContinuousLinearMap` underlying a `PositiveContinuousLinearMap`. -/
add_decl_doc PositiveContinuousLinearMap.toContinuousLinearMap
/-- The `PositiveLinearMap` underlying a `PositiveContinuousLinearMap`. -/
add_decl_doc PositiveContinuousLinearMap.toPositiveLinearMap
namespace PositiveContinuousLinearMap

section General

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [TopologicalSpace E₁] [TopologicalSpace E₂]

instance : FunLike (E₁ →P[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : ContinuousLinearMapClass (E₁ →P[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'
  map_continuous f := f.cont

instance : OrderHomClass (E₁ →P[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

initialize_simps_projections PositiveContinuousLinearMap (toFun → apply)

@[ext]
lemma ext {f g : E₁ →P[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →P[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →P[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  _root_.map_nonneg f hx

section Comp

variable [AddCommMonoid E₃] [PartialOrder E₃] [Module R E₃] [TopologicalSpace E₃]

/-- Composition of positive continuous linear maps. -/
@[simps!]
def comp (g : E₂ →P[R] E₃) (f : E₁ →P[R] E₂) : E₁ →P[R] E₃ where
  toPositiveLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  cont := g.cont.comp f.cont

end Comp

section ofClass

variable {F : Type*} [FunLike F E₁ E₂] [ContinuousLinearMapClass F R E₁ E₂] [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
def ofClass (f : F) : E₁ →P[R] E₂ where
  toPositiveLinearMap := f
  cont := map_continuous f

@[simp]
lemma coe_ofClass (f : F) : ⇑(ofClass f) = f := rfl

end ofClass


@[simp]
lemma coe_toPositiveLinearMap (f : E₁ →P[R] E₂) :
    (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl

@[simp]
lemma coe_toContinuousLinearMap (f : E₁ →P[R] E₂) :
    (f.toContinuousLinearMap : E₁ → E₂) = f :=
  rfl

lemma toPositiveLinearMap_injective :
    Function.Injective (fun f ↦ f.toPositiveLinearMap : (E₁ →P[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

lemma toContinuousLinearMap_injective :
    Function.Injective (fun f ↦ f.toContinuousLinearMap : (E₁ →P[R] E₂) → (E₁ →L[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

instance : Zero (E₁ →P[R] E₂) where
  zero := .mk (0 : E₁ →ₚ[R] E₂) <| by fun_prop

@[simp]
lemma toPositiveLinearMap_zero : (0 : E₁ →P[R] E₂).toPositiveLinearMap = 0 :=
  rfl

@[simp]
lemma toContinuousLinearMap_zero : (0 : E₁ →P[R] E₂).toContinuousLinearMap = 0 :=
  rfl

@[simp]
lemma zero_apply (x : E₁) : (0 : E₁ →P[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂] [ContinuousAdd E₂]

instance : Add (E₁ →P[R] E₂) where
  add f g := .mk (f.toPositiveLinearMap + g.toPositiveLinearMap) <|
    show Continuous (fun x ↦ f x + g x) by fun_prop

@[simp]
lemma toPositiveLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toPositiveLinearMap = f.toPositiveLinearMap + g.toPositiveLinearMap := by
  rfl

@[simp]
lemma toContinuousLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := by
  rfl

@[simp]
lemma add_apply (f g : E₁ →P[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

instance : SMul ℕ (E₁ →P[R] E₂) where
  smul n f := .mk (n • f.toPositiveLinearMap) <|
    show Continuous (fun x ↦ n • f x) by fun_prop

@[simp]
lemma toPositiveLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toPositiveLinearMap = n • f.toPositiveLinearMap :=
  rfl

@[simp]
lemma toContinuousLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toContinuousLinearMap = n • f.toContinuousLinearMap :=
  rfl

@[simp]
lemma nsmul_apply (f : E₁ →P[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

instance : AddCommMonoid (E₁ →P[R] E₂) :=
  toPositiveLinearMap_injective.addCommMonoid _ toPositiveLinearMap_zero toPositiveLinearMap_add
    toPositiveLinearMap_nsmul

end General

section AddGroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [TopologicalSpace E₂]
  [Module R E₁] [Module R E₂]

/-- Define a continuous positive map from a continuous linear map that maps
nonnegative elements to nonnegative elements -/
def mk₀ (f : E₁ →L[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →P[R] E₂ where
  toPositiveLinearMap := .mk₀ f.toLinearMap hf
  cont := f.cont

@[simp]
lemma mk₀_apply (f : E₁ →L[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) (x : E₁) :
    mk₀ f hf x = f x := rfl

end AddGroup

section StarHomClass
open scoped ComplexStarModule

variable {A₁ A₂ : Type*} [AddCommGroup A₁] [Module ℂ A₁]
    [PartialOrder A₁] [StarAddMonoid A₁] [SelfAdjointDecompose A₁]
    [NonUnitalRing A₂] [Module ℂ A₂]
    [StarRing A₂] [PartialOrder A₂] [StarOrderedRing A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [TopologicalSpace A₁] [TopologicalSpace A₂]

instance : StarHomClass (A₁ →P[ℂ] A₂) A₁ A₂ where
  map_star f := map_star f.toPositiveLinearMap

set_option backward.isDefEq.respectTransparency false in
lemma map_realPart (φ : A₁ →P[ℂ] A₂) (x : A₁) :
    φ (ℜ x) = ℜ (φ x) := by
  simp [realPart_apply_coe, map_star]

set_option backward.isDefEq.respectTransparency false in
lemma map_imaginaryPart (φ : A₁ →P[ℂ] A₂) (x : A₁) :
    φ (ℑ x) = ℑ (φ x) := by
  simp [imaginaryPart_apply_coe, map_star]

end StarHomClass

end PositiveContinuousLinearMap
