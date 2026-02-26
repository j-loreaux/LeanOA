import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Group.Defs

namespace OrderIso

-- #35266 fixes this in Mathlib.

variable {α β : Type*} [Preorder α] [Preorder β]

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
that `g` is the inverse of `f`. -/
@[simps apply]
def ofHomInv' (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ ≤ g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
theorem ofHomInv'_symm_apply (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
    (a : β) : (ofHomInv f g h₁ h₂).symm a = g a := rfl

end OrderIso


-- the rest of this is new material for `OrderHom`s.

namespace OrderHom

variable {α : Type*} [Preorder α]

instance : Mul (α →o α) where mul f g := f.comp g
instance : One (α →o α) where one := .id

@[simp] lemma mul_apply (f g : α →o α) (x : α) : (f * g) x = f (g x) := rfl
@[simp] lemma one_apply (x : α) : (1 : α →o α) x = x := rfl

lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
lemma one_eq_id : (1 : α →o α) = .id := rfl

instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom

namespace OrderIso

variable {α : Type*} [Preorder α]

instance : Mul (α ≃o α) where mul f g := g.trans f
instance : One (α ≃o α) where one := refl α
instance : Inv (α ≃o α) where inv := symm

@[simp] lemma mul_apply (f g : α ≃o α) (x : α) : (f * g) x = f (g x) := rfl
@[simp] lemma one_apply (x : α) : (1 : α ≃o α) x = x := rfl
@[simp] lemma inv_apply' (f : α ≃o α) (x : α) : f⁻¹ x = f.symm x := rfl

lemma mul_eq_trans (f g : α ≃o α) : (f * g : α ≃o α) = g.trans f := rfl
lemma one_eq_refl : (1 : α ≃o α) = refl α := rfl
lemma inv_eq_symm (f : α ≃o α) : f⁻¹ = f.symm := rfl

instance : Group (α ≃o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]
  inv_mul_cancel f := by simp [DFunLike.ext_iff]

end OrderIso
