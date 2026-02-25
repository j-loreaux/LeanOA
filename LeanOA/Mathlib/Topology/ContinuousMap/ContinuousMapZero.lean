import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import LeanOA.Mathlib.Algebra.Star.StarAlgHom

namespace ContinuousMapZero

/-- The star algebra equivalence between `C(Y, R)₉` and `C(X, R)₀` given by precomposing
with a homeomorphism `X ≃ₜ Y` mapping `0` to `0`. -/
@[simps!]
def starAlgEquiv_precomp {X Y : Type*} (R : Type*) [Zero X] [Zero Y]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]
    [CommSemiring R] [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R]
    (f : X ≃ₜ Y) (hf : f 0 = 0) :
    C(Y, R)₀ ≃⋆ₐ[R] C(X, R)₀ :=
  StarAlgEquiv.ofHomInv'
    (nonUnitalStarAlgHom_precomp R ⟨f, hf⟩)
    (nonUnitalStarAlgHom_precomp R ⟨f.symm, by simpa using congr(f.symm $hf.symm)⟩)
    (by ext; simp) (by ext; simp)

@[simp]
theorem coe_comp {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]
    (g : C(Y, R)₀) (f : C(X, Y)₀) :
    g.comp f = g ∘ f :=
  rfl

end ContinuousMapZero
