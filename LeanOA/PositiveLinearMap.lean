import Mathlib.Algebra.Order.Module.PositiveLinearMap


namespace PositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂]

@[simp]
lemma coe_toLinearMap (f : E₁ →ₚ[R] E₂) : (f.toLinearMap : E₁ → E₂) = f :=
  rfl

lemma toLinearMap_injective : Function.Injective (toLinearMap : (E₁ →ₚ[R] E₂) → (E₁ →ₗ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

instance : Zero (E₁ →ₚ[R] E₂) where
  zero := .mk (0 : E₁ →ₗ[R] E₂) fun _ ↦ by simp

@[simp]
lemma toLinearMap_zero : (0 : E₁ →ₚ[R] E₂).toLinearMap = 0 :=
  rfl

@[simp]
lemma zero_apply (x : E₁) : (0 : E₁ →ₚ[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂]

instance : Add (E₁ →ₚ[R] E₂) where
  add f g := .mk (f.toLinearMap + g.toLinearMap) fun _ _ h ↦
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]
lemma toLinearMap_add (f g : E₁ →ₚ[R] E₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := by
  rfl

@[simp]
lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

instance : SMul ℕ (E₁ →ₚ[R] E₂) where
  smul n f := .mk (n • f.toLinearMap) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]
lemma toLinearMap_nsmul (f : E₁ →ₚ[R] E₂) (n : ℕ) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

@[simp]
lemma nsmul_apply (f : E₁ →ₚ[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

instance : AddCommMonoid (E₁ →ₚ[R] E₂) :=
  toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

end PositiveLinearMap
