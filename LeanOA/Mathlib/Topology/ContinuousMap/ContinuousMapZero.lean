import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import LeanOA.Mathlib.Algebra.Star.StarAlgHom

namespace ContinuousMapZero
variable {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]

/-- A version of `Pi.single` as an element in `C(A, Y)₀` where `single i x 0 = 0`. -/
noncomputable abbrev single [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A] (i : A)
    (x : Y) : C(A, Y)₀ where
  toFun j := if j = 0 then 0 else (Pi.single i x : A → Y) j
  map_zero' := by simp

lemma single_def [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) (j : A) :
    single i x j = if j = 0 then 0 else (Pi.single i x : A → Y) j := rfl

@[simp] lemma single_apply_of_ne_zero [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) {j : A} (hj : j ≠ 0) : single i x j = (Pi.single i x : A → Y) j := by simp_all

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
