import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Topology.Algebra.Module.LinearMap

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

namespace PositiveContinuousLinearMap

section General

variable {R E₁ E₂ : Type*} [Semiring R]
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

section ofClass

variable {F : Type*} [FunLike F E₁ E₂] [ContinuousLinearMapClass F R E₁ E₂] [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
def ofClass (f : F) : E₁ →P[R] E₂ where
  toPositiveLinearMap := f
  cont := map_continuous f

@[simp]
lemma coe_ofClass (f : F) : ⇑(ofClass f) = f := rfl

end ofClass

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

end PositiveContinuousLinearMap
