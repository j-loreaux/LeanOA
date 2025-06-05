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


section BorelSpace

open BorelSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def support (μ : MeasureTheory.Measure X) : Set X := {x : X | ∀ U ∈ nhds x, μ (interior U) > 0}

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

def ess_range (μ : MeasureTheory.Measure X) (f : X → Y) : Set Y :=
  support (MeasureTheory.Measure.map f μ)

end BorelSpace

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

section AEEqFun

variable {β : Type*} [TopologicalSpace β] [MulOneClass β] [ContinuousMul β]

theorem AEEqFun.one_mul (f : α →ₘ[μ] β) : 1 * f = f := by
   ext
   filter_upwards [coeFn_mul 1 f, coeFn_one (β := β)] with x hx1 hx2
   simp [hx1, hx2]

theorem AEEqFun.one_smul (f : α →ₘ[μ] β) : (1 : α →ₘ[μ] β) • f = f := by simp only [smul_eq_mul,
  AEEqFun.one_mul]

end AEEqFun

open scoped ENNReal

/- These sections are not well named. -/

section NormedRing

variable {R : Type*} [NormedRing R]

section Mul

noncomputable instance Linfty.instMul : Mul (Lp R ∞ μ) where
  mul f g := f • g

end Mul

section Const

/-- Note, does not require `IsFiniteMeasure` instance. -/
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

instance Linfty.instOne : One (Lp R ∞ μ) where
  one := ⟨MemLp.toLp (fun (_ : α) => (1 : R)) (memLp_top_const (μ := μ) 1), SetLike.coe_mem _⟩

theorem Linfty.coeFn_one : ⇑(1 : Lp R ∞ μ) =ᶠ[ae μ] 1 := coeFn_const ..

theorem Linfty.one_smul (f : Lp R ∞ μ) : (1 : Lp R ∞ μ) • f = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) 1 f] with x hx1 hx2
  simp [- smul_eq_mul, hx1, hx2]

theorem Linfty.smul_one (f : Lp R ∞ μ) : f • (1 : Lp R ∞ μ) = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f (1 : Lp R ∞ μ)] with x hx1 hx2
  rw [hx2, Pi.smul_apply', hx1, Pi.one_apply]
  simp

end One

section MulOneClass

noncomputable instance Linfty.instMulOneClass : MulOneClass (Lp R ∞ μ) where
  one := 1
  one_mul := one_smul
  mul_one := smul_one

end MulOneClass

section Semigroup

noncomputable instance Linfty.instSemigroup : Semigroup (Lp R ∞ μ) where
  mul f g := f * g
  mul_assoc := by
    intro f g h
    ext
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) (f * g) h,
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f  (g * h),
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f g,
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) g h] with x hx1 hx2 hx3 hx4
    rw [smul_eq_mul] at *
    simp [hx1, hx2, hx3, hx4, mul_assoc]

end Semigroup

section Distrib

/-- Needs clean up. -/
noncomputable instance Linfty.instDistrib : Distrib (Lp R ∞ μ) where
  left_distrib := by
    intro f g h
    ext
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f (g + h),
      MeasureTheory.Lp.coeFn_add (p := ∞) g h,
      MeasureTheory.Lp.coeFn_add (p := ∞) (f * g) (f * h),
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f g,
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f h] with x h1 h2 h3 h4 h5
    rw [smul_eq_mul] at *
    rw [h3, Pi.add_apply, h4, h5, h1, Pi.smul_apply', h2, Pi.add_apply, Pi.smul_apply', Pi.smul_apply']
    exact DistribSMul.smul_add ..
  right_distrib := by
    intro f g h
    ext
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) (f + g) h, MeasureTheory.Lp.coeFn_add (p := ∞) f g,
       MeasureTheory.Lp.coeFn_add (p := ∞) (f * h) (g * h),  MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f h,
       MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) g h] with x h1 h2 h3 h4 h5
    rw [Pi.smul_apply', h2, Pi.add_apply] at h1
    rw [← smul_eq_mul, h1, h3, Pi.add_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, h4, h5, Pi.smul_apply', Pi.smul_apply']
    exact Module.add_smul ..

end Distrib

section MulZeroClass

/-- Needs clean up. -/
noncomputable instance Linfty.instMulZeroClass : MulZeroClass (Lp R ∞ μ) where
  zero_mul := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) ..,
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) (0 : Lp R ∞ μ) f] with x h1 h2
    rw [h1, ← smul_eq_mul, h2, Pi.smul_apply', h1]
    simp
  mul_zero := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) ..,
      MeasureTheory.Lp.coeFn_lpSMul (𝕜 := R) (p := ∞) (q := ∞) (r := ∞) f (0 : Lp R ∞ μ)] with x h1 h2
    rw [h1, ← smul_eq_mul, h2, Pi.smul_apply', h1]
    simp

end MulZeroClass

noncomputable instance Linfty.instMonoidWithZero : MonoidWithZero (Lp R ∞ μ) where

noncomputable instance Linfty.NonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.instNonAssocSemiring : NonAssocSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.NonUnitalSemiring : NonUnitalSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.Semiring : Semiring (Lp R ∞ μ) where

noncomputable instance Linfty.AddGroupWithOne : AddGroupWithOne (Lp R ∞ μ) where

noncomputable instance Linfty.NonUnitalRing : NonUnitalRing (Lp R ∞ μ) where

noncomputable instance Linfty.Ring : Ring (Lp R ∞ μ) where

end NormedRing

section AEEqFunStar

variable {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

instance : Star (α →ₘ[μ] R) where
  star f := (AEEqFun.comp _ continuous_star f)

lemma AEEqFun.coeFn_star (f : α →ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α → R) :=
   coeFn_comp _ (continuous_star) f

end AEEqFunStar

section AEEqFunNormStar

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

theorem AEEqFun.norm_star {p : ℝ≥0∞} {f : α →ₘ[μ] R} :
    eLpNorm (star f) p μ = eLpNorm f p μ := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [coeFn_star f] with x hx
  simp [hx]

end AEEqFunNormStar

section LpStar

local infixr:25 " →ₛ " => SimpleFunc

instance {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] : Star (α →ₛ R) where
  star f := f.map Star.star

lemma star_apply {R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R] (f : α →ₛ R) (x : α) : (star f) x = star (f x) := rfl

protected theorem _root_.Filter.EventuallyEq.star {α β : Type*} [Star β] {f g : α → β}
    {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x ↦ star (f x)) =ᶠ[l] fun x ↦ star (g x) :=
  h.fun_comp Star.star

@[measurability]
protected theorem StronglyMeasurable.star {β : Type*} [TopologicalSpace β]
    [Star β] [ContinuousStar β] (f : α → β) (hf : StronglyMeasurable f) :
    StronglyMeasurable (star f) :=
  ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

@[simp]
theorem eLpNorm_star {p : ℝ≥0∞} {f : α → R} :
    eLpNorm (star f) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| .of_forall <| by simp

@[simp]
theorem AEEqFun.eLpNorm_star {p : ℝ≥0∞} {f : α →ₘ[μ] R} :
    eLpNorm (star f : α →ₘ[μ] R) p μ = eLpNorm f p μ :=
  eLpNorm_congr_ae (coeFn_star f) |>.trans <| by simp

protected theorem AEStronglyMeasurable.star {f : α → R} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (star f) μ :=
  ⟨star (hf.mk f), hf.stronglyMeasurable_mk.star, hf.ae_eq_mk.star⟩

protected theorem MemLp.star {p : ℝ≥0∞} {f : α → R} (hf : MemLp f p μ) : MemLp (star f) p μ :=
  ⟨hf.1.star, by simpa using hf.2⟩

protected noncomputable instance Lp.Star {p : ℝ≥0∞} : Star (Lp R p μ) where
  star f := ⟨star (f : α →ₘ[μ] R), by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩

end LpStar

section LpInvolutiveStar

section

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

end

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

noncomputable instance InvolutiveStar {p : ℝ≥0∞} : InvolutiveStar (Lp R p μ) where
  star_involutive f := by
     ext
     filter_upwards
     exact congrFun (congrArg AEEqFun.cast <| star_involutive f.1)

end LpInvolutiveStar

section StarMul
section

variable {R : Type*} [NormedRing R] [StarRing R] [NormedStarGroup R]

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

end

variable {R : Type*} [NormedRing R]

lemma Linfty.coeFn_mul (f g : Lp R ∞ μ) : f * g =ᵐ[μ] ⇑f * g :=
  MeasureTheory.Lp.coeFn_lpSMul f g

variable [_root_.StarRing R] [NormedStarGroup R]

lemma Lp.coeFn_star {p : ℝ≥0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star f :=
    (f : α →ₘ[μ] R).coeFn_star

noncomputable instance Linfty.StarMul : StarMul (Lp R ∞ μ) where
  star_mul f g := by
    ext
    filter_upwards [Lp.coeFn_star (f * g), Linfty.coeFn_mul f g,
      Linfty.coeFn_mul (star g) (star f), Lp.coeFn_star f, Lp.coeFn_star g] with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp [hx₁, hx₂, hx₃, hx₄, hx₅]

end StarMul

section StarRing

variable {R : Type*} [NormedRing R] [_root_.StarRing R] [NormedStarGroup R]

noncomputable instance Linfty.StarAddMonoid : StarAddMonoid (Lp R ∞ μ) where
  star_add f g := by
    ext
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with x hx hy hz hw hq
    rw [hy, Pi.star_apply, hx, Pi.add_apply, star_add, hz, Pi.add_apply, hw, hq, Pi.star_apply, Pi.star_apply]

noncomputable instance Linfty.StarRing : StarRing (Lp R ∞ μ) where
  star_add := star_add

end StarRing

section NormedRing

variable {R : Type*} [NormedRing R] [_root_.IsBoundedSMul R R]

noncomputable instance Linfty.NormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le f g := MeasureTheory.Lp.norm_smul_le f g

end NormedRing

section NormedAlgebra

variable {R : Type*} [_root_.NormedRing R] [_root_.IsBoundedSMul R R]
variable {𝕜 : Type u_6} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := fun x y z => Lp.smul_assoc x y z

noncomputable instance Linfty.NormedAlgebra : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  smul c f := c • f
  algebraMap :={
    toFun := fun (c : 𝕜) ↦ c • (1 : Lp R ∞ μ)
    map_one' := MulAction.one_smul 1
    map_mul' := by
      intro a b
      ext
      filter_upwards [Lp.coeFn_smul (E := R) (p := ∞) (a * b) 1, Linfty.coeFn_mul (R := R) (a • 1) (b • 1),
          Lp.coeFn_smul (E := R) (p := ∞) a 1, Lp.coeFn_smul (E := R) (p := ∞) b 1, Linfty.coeFn_one (R := R)] with x hx hy hz hw h1
      rw [hx, Pi.smul_apply, hy, Pi.mul_apply, hz, hw, Pi.smul_apply, h1, Pi.ofNat_apply, Pi.smul_apply, h1, Pi.ofNat_apply, smul_one_mul, mul_smul a b 1]
    map_zero' := zero_smul 𝕜 1
    map_add' := fun x y => Module.add_smul x y 1
  }
  commutes' := by
    dsimp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul, Set.mem_setOf_eq,
      Pi.mul_apply, id_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    intro r f
    ext
    filter_upwards [Linfty.coeFn_mul (r • (1 : Lp R ∞ μ)) f, Linfty.coeFn_mul (R := R) f (r • 1),
      Lp.coeFn_smul (E := R) (p := ∞) r 1, Linfty.coeFn_one (R := R), Lp.coeFn_smul (E := R) (p := ∞) r (1 * f),
      Linfty.coeFn_mul (R := R) 1 f] with x hx hy hz hw hq hv
    simp only [hx, Pi.mul_apply, hz, Pi.smul_apply, hw, Pi.ofNat_apply, smul_eq_mul, mul_one, hy, mul_comm, mul_smul_comm, Algebra.smul_mul_assoc, one_mul]
  smul_def' := by
    dsimp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul, Set.mem_setOf_eq,
      Pi.mul_apply, id_eq, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, smul_one]
    intro r x
    rw [← smul_eq_mul, smul_assoc, one_smul]
  norm_smul_le := fun r x => norm_smul_le r x

end NormedAlgebra

section CStarRing

variable {R : Type*} [NormedRing R]

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
  have : Filter.IsBoundedUnder (· ≤ ·) (MeasureTheory.ae μ) (fun t => ‖f t‖ₑ) := by isBoundedDefault
  convert _root_.ae_le_essSup
  rw [← eLpNormEssSup, ← eLpNorm_exponent_top, ←Lp.enorm_def]
  exact enorm_le_iff_norm_le.symm

variable [StarRing R] [NormedStarGroup R]

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

variable {R : Type*} [_root_.NormedRing R] [_root_.IsBoundedSMul R R]
variable {𝕜 : Type u_6} [NormedField 𝕜] [NormedAlgebra 𝕜 R] [Star 𝕜]
variable [StarRing R] [NormedStarGroup R]

noncomputable instance : StarModule 𝕜 (Lp R ∞ μ) where
  star_smul := by
     intro r a
     rw [@Lp.ext_iff]
     filter_upwards with x
     --Finish this and you'll have a `CStarAlgebra` structure on Linfty. Then you can move on to try to get this
     --is a W* algebra.

end StarModule

section CStarAlgebra

noncomputable instance {R : Type*} [CStarAlgebra R] : CStarAlgebra (Lp R ∞ μ) where

--Go back and omit all names of instances. Let Lean name your instances.

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
