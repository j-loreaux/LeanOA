/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Algebra.Algebra.Quasispectrum
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Borel Functional Calculus Class

We develop the basic definition of the `BorelFunctionalCalculus` class, imitating
`ContinuousFunctionalCalculus`

## Main declarations

+ TBD

# TODO

-/


namespace MeasureTheory
section BorelSpace

open BorelSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def support (μ : Measure X) : Set X := {x : X | ∀ U ∈ nhds x, μ (interior U) > 0}

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

def ess_range (μ : Measure X) (f : X → Y) : Set Y :=
  support (Measure.map f μ)

end BorelSpace

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

section Star

local infixr:25 " →ₛ " => SimpleFunc

variable {R : Type*} [Star R]

instance : Star (α →ₛ R) where
  star f := f.map Star.star

lemma star_apply (f : α →ₛ R) (x : α) : (star f) x = star (f x) := rfl

protected theorem _root_.Filter.EventuallyEq.star {f g : α → R}
    {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x ↦ star (f x)) =ᶠ[l] fun x ↦ star (g x) :=
  h.fun_comp Star.star

variable [TopologicalSpace R] [ContinuousStar R]

@[measurability]
protected theorem StronglyMeasurable.star (f : α → R) (hf : StronglyMeasurable f) :
    StronglyMeasurable (star f) :=
  ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

variable {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

protected theorem AEStronglyMeasurable.star {f : α → R} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (star f) μ :=
  ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

instance : Star (α →ₘ[μ] R) where
  star f := (AEEqFun.comp _ continuous_star f)

lemma AEEqFun.coeFn_star (f : α →ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α → R) :=
   coeFn_comp _ (continuous_star) f

end Star

section NormStar

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

@[simp]
theorem eLpNorm_star {p : ℝ≥0∞} {f : α → R} : eLpNorm (star f) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| .of_forall <| by simp

@[simp]
theorem AEEqFun.eLpNorm_star {p : ℝ≥0∞} {f : α →ₘ[μ] R} : eLpNorm (star f : α →ₘ[μ] R) p μ = eLpNorm f p μ :=
  eLpNorm_congr_ae (coeFn_star f) |>.trans <| by simp

end NormStar

section LpStar

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

protected theorem MemLp.star {p : ℝ≥0∞} {f : α → R} (hf : MemLp f p μ) : MemLp (star f) p μ :=
  ⟨hf.1.star, by simpa using hf.2⟩

protected noncomputable instance {p : ℝ≥0∞} : Star (Lp R p μ) where
  star f := ⟨star (f : α →ₘ[μ] R), by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩

lemma Lp.coeFn_star {p : ℝ≥0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star f :=
    (f : α →ₘ[μ] R).coeFn_star

end LpStar

section LpInvolutiveStar

section AEEqFun

local infixr:25 " →ₛ " => SimpleFunc

variable {R : Type*} [TopologicalSpace R] [InvolutiveStar R] [ContinuousStar R]

instance : InvolutiveStar (α →ₛ R) where
  star_involutive := by
    intro f
    ext x
    simp only [star_apply (star f), star_apply f, star_star]

instance : InvolutiveStar (α →ₘ[μ] R) where
  star_involutive f := by
    ext
    filter_upwards [AEEqFun.coeFn_star (star f), AEEqFun.coeFn_star f] with x hx hy
    simp only [hx, Pi.star_apply, hy, star_star]

end AEEqFun

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

noncomputable instance {p : ℝ≥0∞} : InvolutiveStar (Lp R p μ) where
  star_involutive f := by
     ext
     filter_upwards
     exact congrFun (congrArg AEEqFun.cast <| star_involutive f.1)

end LpInvolutiveStar

section NormedRing

variable {R : Type*} [NormedRing R]

section Mul

noncomputable instance : Mul (Lp R ∞ μ) where
  mul f g := f • g

lemma Linfty.coeFn_mul (f g : Lp R ∞ μ) : f * g =ᵐ[μ] ⇑f * g :=
  Lp.coeFn_lpSMul f g

end Mul

section Const

/-- Note: Unlike for general Lp, this does not require `IsFiniteMeasure` instance. -/
theorem memLinfty_const (c : R) : MemLp (fun _ : α => c) ∞ μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [eLpNorm_const c (ENNReal.top_ne_zero) hμ]
    simp

theorem const_mem_Linfty (c : R) :
    @AEEqFun.const α _ _ μ _ c ∈ Lp R ∞ μ :=
  (memLinfty_const c).eLpNorm_mk_lt_top

def Linfty.const : R →+ Lp R ∞ μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Linfty c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma Linfty.const_val (c : R) : (Linfty.const c).1 = AEEqFun.const (β := R) (μ := μ) α c := rfl

lemma Linfty.coeFn_const (c : R) : Linfty.const (μ := μ) c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

end Const

section One

section AEEqFun

variable {β : Type*} [TopologicalSpace β] [MulOneClass β] [ContinuousMul β]

theorem AEEqFun.one_mul (f : α →ₘ[μ] β) : 1 * f = f := by
  ext
  filter_upwards [coeFn_mul 1 f, coeFn_one (β := β)] with x hx1 hx2
  simp [hx1, hx2]

theorem AEEqFun.one_smul (f : α →ₘ[μ] β) : (1 : α →ₘ[μ] β) • f = f := by
  simp only [smul_eq_mul, AEEqFun.one_mul]

end AEEqFun


instance Linfty.instOne : One (Lp R ∞ μ) where
  one := ⟨MemLp.toLp (fun (_ : α) => (1 : R)) (memLp_top_const (μ := μ) 1), SetLike.coe_mem _⟩

theorem Linfty.coeFn_one : ⇑(1 : Lp R ∞ μ) =ᶠ[ae μ] 1 := coeFn_const ..

theorem Linfty.one_smul (f : Lp R ∞ μ) : (1 : Lp R ∞ μ) • f = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    Linfty.coeFn_mul 1 f] with x hx1 hx2
  simp [hx1, hx2]

theorem Linfty.smul_one (f : Lp R ∞ μ) : f • (1 : Lp R ∞ μ) = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    Linfty.coeFn_mul f (1 : Lp R ∞ μ)] with x hx1 hx2
  simp_all only [Pi.one_apply, Pi.mul_apply, mul_one, smul_eq_mul]

end One

section MulOneClass

noncomputable instance : MulOneClass (Lp R ∞ μ) where
  one_mul := Linfty.one_smul
  mul_one := Linfty.smul_one

end MulOneClass

section Semigroup

noncomputable instance : Semigroup (Lp R ∞ μ) where
  mul f g := f * g
  mul_assoc := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul (f * g) h, Linfty.coeFn_mul f  (g * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul g h] with x hx1 hx2 hx3 hx4
    simp [hx1, hx2, hx3, hx4, mul_assoc]

end Semigroup

section Distrib

/-- Needs clean up. -/
noncomputable instance : Distrib (Lp R ∞ μ) where
  left_distrib := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul f (g + h),
      Lp.coeFn_add (p := ∞) g h, Lp.coeFn_add (p := ∞) (f * g) (f * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul f h] with x h1 h2 h3 h4 h5
    rw [h3, Pi.add_apply, h4, h5, h1, Pi.mul_apply, h2, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, mul_add]
  right_distrib := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul (f + g) h, Lp.coeFn_add (p := ∞) f g,
       Lp.coeFn_add (p := ∞) (f * h) (g * h), Linfty.coeFn_mul f h,
       Linfty.coeFn_mul g h] with x h1 h2 h3 h4 h5
    rw [Pi.mul_apply, h2, Pi.add_apply] at h1
    rw [h1, h3, Pi.add_apply, h4, h5, Pi.mul_apply, Pi.mul_apply, add_mul]

end Distrib

section MulZeroClass

/-- Needs clean up. -/
noncomputable instance : MulZeroClass (Lp R ∞ μ) where
  zero_mul := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) (p := ∞) ..,
      Linfty.coeFn_mul (0 : Lp R ∞ μ) f] with x h1 h2
    simp_all only [ZeroMemClass.coe_zero, Pi.zero_apply, Pi.mul_apply, zero_mul]
  mul_zero := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) (p := ∞) ..,
      Linfty.coeFn_mul f (0 : Lp R ∞ μ)] with x h1 h2
    simp_all only [ZeroMemClass.coe_zero, Pi.zero_apply, Pi.mul_apply, mul_zero]

end MulZeroClass

noncomputable instance : MonoidWithZero (Lp R ∞ μ) where

noncomputable instance : NonUnitalNonAssocSemiring (Lp R ∞ μ) where

noncomputable instance : NonAssocSemiring (Lp R ∞ μ) where

noncomputable instance : NonUnitalSemiring (Lp R ∞ μ) where

noncomputable instance : Semiring (Lp R ∞ μ) where

noncomputable instance : AddGroupWithOne (Lp R ∞ μ) where

noncomputable instance : NonUnitalRing (Lp R ∞ μ) where

noncomputable instance : Ring (Lp R ∞ μ) where

section StarMul
section AEEqFun

variable [StarRing R] [NormedStarGroup R]

local infixr:25 " →ₛ " => SimpleFunc

instance : StarMul (α →ₛ R) where
  star_mul := by
    intro f g
    ext
    simp only [star_apply, SimpleFunc.coe_mul, Pi.mul_apply, star_mul]

instance : StarMul (α →ₘ[μ] R) where
  star_mul f g := by
    ext
    filter_upwards [AEEqFun.coeFn_star (f * g), AEEqFun.coeFn_mul f g, AEEqFun.coeFn_mul (star g) (star f), AEEqFun.coeFn_star f,
         AEEqFun.coeFn_star g] with x hx hy hz h1 h2
    simp only [hx, Pi.star_apply, hy, Pi.mul_apply, hz, h1, h2, star_mul]

instance : StarAddMonoid (α →ₘ[μ] R) where
  star_add f g:= by
    ext
    filter_upwards [AEEqFun.coeFn_star (f + g), AEEqFun.coeFn_add (star f) (star g), AEEqFun.coeFn_add f g, AEEqFun.coeFn_star f, AEEqFun.coeFn_star g] with x hx hy hz hq hw
    simp only [hx, Pi.star_apply, hz, Pi.add_apply, star_add, hy, hq, hw]

end AEEqFun

variable [StarRing R] [NormedStarGroup R]

noncomputable instance : StarMul (Lp R ∞ μ) where
  star_mul f g := by
    ext
    filter_upwards [Lp.coeFn_star (f * g), Linfty.coeFn_mul f g,
      Linfty.coeFn_mul (star g) (star f), Lp.coeFn_star f, Lp.coeFn_star g] with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp [hx₁, hx₂, hx₃, hx₄, hx₅]

end StarMul

section StarRing

variable [StarRing R] [NormedStarGroup R]

noncomputable instance : StarAddMonoid (Lp R ∞ μ) where
  star_add f g := by
    ext
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with x hx hy hz hw hq
    rw [hy, Pi.star_apply, hx, Pi.add_apply, star_add, hz, Pi.add_apply, hw, hq, Pi.star_apply, Pi.star_apply]

noncomputable instance : StarRing (Lp R ∞ μ) where
  star_add := star_add

end StarRing

section IsBoundedSMul

variable [IsBoundedSMul R R]

noncomputable instance : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le f g := Lp.norm_smul_le f g

section Algebra

variable {𝕜 : Type u_6} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := Lp.smul_assoc

instance : SMulCommClass 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_comm := Lp.smul_comm

noncomputable instance : Algebra 𝕜 (Lp R ∞ μ) := Algebra.ofModule (smul_mul_assoc) (mul_smul_comm)

end Algebra

section NormedAlgebra

variable {𝕜 : Type u_6} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

noncomputable instance : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  norm_smul_le := norm_smul_le

end NormedAlgebra

section CStarRing

open scoped NNReal
open ENNReal

lemma enorm_le_of_ae_enorm_le (f : Lp R ∞ μ) (c : ℝ≥0∞) (hf : ∀ᵐ(x : α) ∂μ, ‖f x‖ₑ ≤ c) : ‖f‖ₑ ≤ c := by
  have := essSup_le_of_ae_le _ hf
  simpa only [Lp.enorm_def, eLpNorm_exponent_top, ge_iff_le]

lemma nnnorm_le_of_ae_nnnorm_le (f : Lp R ∞ μ) (c : ℝ≥0) (hf : ∀ᵐ(x : α) ∂μ, ‖f x‖₊ ≤ c) : ‖f‖₊ ≤ c := by
  have hf' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c := by filter_upwards [hf]; simp
  simpa only [enorm_le_coe] using enorm_le_of_ae_enorm_le f c hf'

lemma norm_le_of_ae_norm_le (f : Lp R ∞ μ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ᵐ(x : α) ∂μ, ‖f x‖ ≤ c) : ‖f‖ ≤ c :=
  nnnorm_le_of_ae_nnnorm_le f ⟨c, hc⟩ hf

lemma ae_norm_le_norm (f : Lp R ∞ μ) : ∀ᵐ(x : α) ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have : Filter.IsBoundedUnder (· ≤ ·) (ae μ) (fun t => ‖f t‖ₑ) := by isBoundedDefault
  convert _root_.ae_le_essSup
  rw [← eLpNormEssSup, ← eLpNorm_exponent_top, ←Lp.enorm_def]
  exact enorm_le_iff_norm_le.symm

/- The next result only needs R to be a `NormedStarGroup`, but we have `R` as a `NormedRing`. Just a warning. -/
variable [StarRing R]

instance [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (by positivity) (by positivity), Real.sqrt_eq_rpow]
    apply norm_le_of_ae_norm_le _ _ (by positivity)
    filter_upwards [ae_norm_le_norm (star f * f), Lp.coeFn_star f, Linfty.coeFn_mul (star f) f] with x hx hx_star hx_mul
    refine Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (norm_nonneg _) (by norm_num)|>.mp ?_
    simp only [one_div, inv_inv, Real.rpow_two]
    convert hx
    simp [sq, hx_mul, hx_star]
    exact CStarRing.norm_star_mul_self.symm

end CStarRing

section StarModule

variable {𝕜 : Type u_6} [NormedField 𝕜] [NormedAlgebra 𝕜 R] [Star 𝕜]
variable [StarRing R] [NormedStarGroup R] [StarModule 𝕜 R]

noncomputable instance : StarModule 𝕜 (α →ₘ[μ] R) where
  star_smul := by
     intro c f
     refine AEEqFun.ext_iff.mpr ?_
     filter_upwards [AEEqFun.coeFn_star (c • f), AEEqFun.coeFn_smul c f, (AEEqFun.coeFn_smul (star c) (star f)).symm, AEEqFun.coeFn_star f] with x hstar1 hsmul1 hsmul2 hstar2
     simp only [hstar1, Pi.star_apply, hsmul1, Pi.smul_apply, star_smul, ← hsmul2, hstar2]

noncomputable instance : StarModule 𝕜 (Lp R ∞ μ) where
  star_smul := by
    intro r f
    refine SetLike.coe_eq_coe.mp ?_
    exact star_smul  (R := 𝕜) (A := α →ₘ[μ] R) r f

end StarModule

end IsBoundedSMul

end NormedRing
section CStarAlgebra

noncomputable instance {R : Type*} [CStarAlgebra R] : CStarAlgebra (Lp R ∞ μ) where

end CStarAlgebra



section BFC

class BorelFunctionalCalculus {A : Type*} (p : outParam (A → Prop))
    [CStarAlgebra A] [WStarAlgebra A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum ℂ a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum ℂ a).Nonempty
  exists_bfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A,
    IsClosedEmbedding φ ∧ φ ((ContinuousMap.id ℂ).restrict <| spectrum ℂ a) = a ∧
      (∀ f, spectrum ℂ (φ f) = Set.range f) ∧ ∀ f, p (φ f)

--We need a type synonym for Lp (spectrum ℂ a) ∞ μ with the weak * topology coming from the predual Lp (spectrum ℂ a) 1 μ.
--This Lp (spectrum ℂ a) ∞ μ must also be a *--algebra..this should somehow be in the type synonym.
--Once we have this, we need to replace all instances of C(spectrum ℂ a, ℂ) with Lp (spectrum ℂ a) ∞ μ.
--Still need the essential range for this spectrum result.

end BFC
