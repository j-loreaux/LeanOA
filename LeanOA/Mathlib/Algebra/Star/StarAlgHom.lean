module

public import Mathlib.Algebra.Star.StarAlgHom

@[expose] public section

namespace StarAlgEquiv

section RestrictScalars

-- this should replace the existing `StarAlgEquiv.restrictScalars`

variable (R : Type*) {S A B : Type*} [CommSemiring R] [CommSemiring S]
  [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [SMul R S] [Module S A] [Module S B]
  [Module R A] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B] [Star A] [Star B]

/-- Restrict the scalar ring of a star algebra equivalence. -/
@[simps]
def restrictScalars' (f : A ≃⋆ₐ[S] B) : A ≃⋆ₐ[R] B :=
  { (f : A →ₗ[S] B).restrictScalars R, f with
    toFun := f }

theorem restrictScalars_injective' :
    Function.Injective (StarAlgEquiv.restrictScalars' R : (A ≃⋆ₐ[S] B) → A ≃⋆ₐ[R] B) :=
  fun f g h => StarAlgEquiv.ext fun x =>
    show f.restrictScalars' R x = g.restrictScalars' R x from DFunLike.congr_fun h x

end RestrictScalars
section NonUnital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
  [NonUnitalNonAssocSemiring A₃] [DistribMulAction R A₃] [Star A₃]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']
  [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
  [NonUnitalNonAssocSemiring A₃'] [DistribMulAction R A₃'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

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
