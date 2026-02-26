import Mathlib.Algebra.Star.StarAlgHom

namespace StarAlgEquiv

section NonUnital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
  [NonUnitalNonAssocSemiring A₃] [DistribMulAction R A₃] [Star A₃]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']
  [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
  [NonUnitalNonAssocSemiring A₃'] [DistribMulAction R A₃'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a non-unital star algebra homomorphism. -/
@[simps]
def toNonUnitalStarAlgHom : A₁ →⋆ₙₐ[R] A₂ where
  toFun := e
  map_add' := map_add e
  map_zero' := map_zero e
  map_mul' := map_mul e
  map_smul' := map_smul e
  map_star' := map_star e

@[simp]
lemma toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toNonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom =
      (e₁.trans e₂).toNonUnitalStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₙₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₙₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (A₁ →⋆ₙₐ[R] A₂) ≃ (A₁' →⋆ₙₐ[R] A₂') where
  toFun f := (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem arrowCongr'_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₃) :
    arrowCongr' e₁ e₃ (g.comp f) = (arrowCongr' e₂ e₃ g).comp (arrowCongr' e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr'_refl : arrowCongr' .refl .refl = Equiv.refl (A₁ →⋆ₙₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr'_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr'_symm (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of non-unital star algebra homomorphisms. -/
@[simps]
def ofHomInv' {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)
  map_mul' := map_mul f
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end NonUnital

section Unital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*}
  [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
  [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
  [Star A₁] [Star A₂] [Star A₃]
  [Star A₁'] [Star A₂'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a star algebra homomorphism. -/
@[simps]
def toStarAlgHom : A₁ →⋆ₐ[R] A₂ where
  toFun := e
  map_add' := map_add e
  map_zero' := map_zero e
  map_mul' := map_mul e
  map_one' := map_one e
  commutes' := e.toAlgEquiv.commutes
  map_star' := map_star e

@[simp]
lemma toStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toStarAlgHom.comp e₁.toStarAlgHom = (e₁.trans e₂).toStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ →⋆ₐ[R] A₂) ≃ (A₁' →⋆ₐ[R] A₂') where
  toFun f := (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem arrowCongr_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr_refl : arrowCongr .refl .refl = Equiv.refl (A₁ →⋆ₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr_symm (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of star algebra homomorphisms. -/
@[simps]
def ofHomInv {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (g : B →⋆ₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)
  map_mul' := map_mul f
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end Unital

end StarAlgEquiv
