import LeanOA.Demo.Misc
import Mathlib.Analysis.CStarAlgebra.Hom

set_option aesop.dev.statefulForward false

open CStarAlgebra Unitization Function

variable {A B : Type*}

/-- The `ℝ`-spectrum of a selfadjoint element is preserved under an
injective ⋆-homomorphism of (unital) C⋆-algebras. -/
example [CStarAlgebra A] [CStarAlgebra B] {a : A}
    (ha : IsSelfAdjoint a) (φ : A →⋆ₐ[ℂ] B) (hφ : Injective φ) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  -- one inclusion is immediate since `φ` is an algebra homomorphism.
  refine Set.Subset.antisymm
    (AlgHom.spectrum_apply_subset (φ.restrictScalars ℝ) a)
    fun x hx ↦ ?_
  /- we prove the reverse inclusion by contradiction, so assume that
  `x ∈ spectrum ℝ a`, but `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's
  lemma we can get a continuous function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
    (spectrum.isClosed (φ a)) (isClosed_singleton (x := x)) (by simpa)
  /- it suffices to show that `φ (f a) = 0`, for if so, then `f a = 0`
  by injectivity of `φ`, and hence `f = 0` on `spectrum ℝ a`,
  contradicting the fact that `f x = 1`. -/
  suffices φ (cfc f a) = 0 by
    rw [map_eq_zero_iff φ hφ, ← cfc_zero ℝ a, cfc_eq_cfc_iff_eqOn] at this
    aesop
  /- Finally, `φ (f a) = f (φ a) = 0`, where the last equality
  follows since `f = 0` on `spectrum ℝ (φ a)`. -/
  calc φ (cfc f a) = cfc f (φ a) := StarAlgHomClass.map_cfc φ f a
    _ = cfc (0 : ℝ → ℝ) (φ a) := cfc_congr h_eqOn
    _ = 0 := by simp

-- of course, the complex spectra are equal too.
example [CStarAlgebra A] [CStarAlgebra B] {a : A}
    (ha : IsSelfAdjoint a) (φ : A →⋆ₐ[ℂ] B) (hφ : Injective φ) :
    spectrum ℂ (φ a) = spectrum ℂ a := by
  -- Since `a` and `φ a` are selfadjoint, their `ℂ`-spectra are the
  -- images of their `ℝ`-spectra, -- which coincide by the previous result.
  simpa [- Complex.coe_algebraMap, ha.spectrumRestricts.algebraMap_image,
    (ha.map φ).spectrumRestricts.algebraMap_image]
    using congr(algebraMap ℝ ℂ '' $(ha.map_spectrum_real φ hφ))

/-- A ⋆-algebra homomorphism of C⋆-algebras is isometric. -/
example [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (hφ : Injective φ) (a : A) :
    ‖φ a‖ = ‖a‖ := by
  /- Since passing to the unitization is functorial, and it is an
  isometric embedding, we may assume that `φ` is a unital star
  algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices ∀ {ψ : A⁺¹ →⋆ₐ[ℂ] B⁺¹} (_ : Injective ψ) (a : A⁺¹), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starMap_injective hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show
  -- `‖ψ (star a * a)‖ = ‖star a * a‖`
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it has the same `ℝ`-spectrum
  as `ψ (star a * a)`.  For selfadjoint elements, the spectral radius
  over `ℝ` coincides with the norm, hence
  `‖ψ (star a * a)‖ = ‖star a * a‖`. -/
  have ha : IsSelfAdjoint (star a * a) := by aesop
  calc
    ‖ψ (star a * a)‖ = (spectralRadius ℝ (ψ (star a * a))).toReal :=
      ha.map ψ |>.toReal_spectralRadius_eq_norm.symm
    _ = (spectralRadius ℝ (star a * a)).toReal := by
      simp only [spectralRadius, ha.map_spectrum_real ψ hψ]
    _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm
