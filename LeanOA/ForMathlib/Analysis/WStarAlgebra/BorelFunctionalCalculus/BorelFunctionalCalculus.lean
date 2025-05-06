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

variable [NormedRing R]

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

variable [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

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

variable [TopologicalSpace R] [InvolutiveStar R] [ContinuousStar R]

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

noncomputable instance Linfty.StarRing : StarRing (Lp R ∞ μ) where
  star_add := sorry

noncomputable instance Linfty.NormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq := sorry
  norm_mul_le := sorry

-- Some bizarre things are starting to happen. We are declaring instances that Lean can't find. There must be
-- confusion. It seems to have something to do with the complex `SMul`.



#synth SMul R (Lp R ∞ μ)

end StarMul

#

noncomputable instance Linfty.ComplexAlgebra : Algebra ℂ (Lp R ∞ μ) where

#synth Algebra ℂ (Lp R ∞ μ)

variable [CompleteSpace R]

noncomputable instance Linfty.CompleteSpace : CompleteSpace (Lp R ∞ μ) where

noncomputable instance Linfty.NormedAlgebra : NormedAlgebra ℂ (Lp R ∞ μ) where

#synth Algebra ℂ (Lp R ∞ μ)
#synth NormedAlgebra ℂ (Lp R ∞ μ)


#synth ENNReal.HolderTriple ⊤ ⊤ ⊤
#synth HSMul (Lp R ⊤ μ) (Lp R ⊤ μ) (Lp R ⊤ μ)
#synth AddCommGroup (Lp R ⊤ μ)
#synth Norm (Lp R ⊤ μ)
#synth MetricSpace (Lp R ⊤ μ)
#synth HMul (Lp R ⊤ μ) (Lp R ⊤ μ) (Lp R ⊤ μ)
#synth SMul (Lp R ⊤ μ) (Lp R ⊤ μ) --should be ok because defeq to the other HSMul
#synth MulOneClass (Lp R ⊤ μ)
#synth Semigroup (Lp R ⊤ μ)
#synth NonAssocSemiring (Lp R ⊤ μ)
#synth NonUnitalSemiring (Lp R ⊤ μ)
#synth Monoid (Lp R ⊤ μ)
#synth MonoidWithZero (Lp R ⊤ μ)
#synth Semiring (Lp R ⊤ μ)
#synth AddGroupWithOne (Lp R ⊤ μ)
#synth Ring (Lp R ∞ μ)
#synth Star (Lp R ∞ μ)
#synth InvolutiveStar (Lp R ∞ μ)
#synth CompleteSpace (Lp R ∞ μ)
#synth Algebra ℂ (Lp R ∞ μ)
section LpArithmetic

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology MeasureTheory Uniformity symmDiff

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-Since we are having difficulties with the general construction, let's just try to prove a theorem
saying that if one looks at the a.e. class of the product of two essentially bounded functions,
then the resulting function is also essentially bounded. We then can move on to see how to best say this
with instances, etc.-/
namespace Memℒp

variable {f g : α → ℂ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ)



--The following result needs a better name. The use `infty_mul` means something like `⊤ * a` in the library so that's no good.
-- What we want is `Memℒ∞.mul`, I think.
theorem MemLinfty.mul {f g : α → ℂ} (hg : MemLp g ⊤ μ) (hf : MemLp f ⊤ μ)  : MemLp (f * g) ⊤ μ := MemLp.mul hg hf

#check (MemLp.toLp (MemLinfty.mul hg hf)).2

theorem Mem {f g : α → ℂ} (hg : MemLp g ⊤ μ) (hf : MemLp f ⊤ μ) : Prop := (MemLp.toLp MemLinfty.mul hg hf).2



  --⟨ MeasureTheory.AEStronglyMeasurable.mul (aestronglyMeasurable hf) (aestronglyMeasurable hg),
  -- by simp only [eLpNorm, ENNReal.top_ne_zero, ↓reduceIte, eLpNormEssSup, Pi.mul_apply, nnnorm_mul, ENNReal.coe_mul]
  --    exact LE.le.trans_lt (ENNReal.essSup_mul_le (fun x ↦ ‖f x‖₊) (fun x ↦ ‖g x‖₊)) (WithTop.mul_lt_top hf.2 hg.2) ⟩

--The above is working too hard. We already have  `MeasureTheory.Memℒp.mul` in the library.

--Now we need to define the multiplication on the L infty space itself. But this is in an `AddSubgroup`, so is a bit unusual...

-- We also have `MeasureTheory.AEEqFun.instMul` for a multiplication instance at the level of classes of measurable functions.

noncomputable def ml (f g : α →ₘ[μ] ℂ) (hf : f ∈  Lp ℂ ⊤ μ) (hg : g ∈  Lp ℂ ⊤ μ) := MemLp.toLp _ (MemLinfty.mul ((MeasureTheory.Lp.mem_Lp_iff_memℒp).mp hf) ((MeasureTheory.Lp.mem_Lp_iff_memℒp).mp hg))


noncomputable instance LinftyMul : Mul (Lp ℂ ⊤ μ) where
  mul := fun
    | .mk f hf => fun
      | .mk g hg => .mk (f * g) (by
        have H := MemLp.toLp (f * g) (MemLinfty.mul ((MeasureTheory.Lp.mem_Lp_iff_memℒp).mp hf) ((MeasureTheory.Lp.mem_Lp_iff_memℒp).mp hg)))



--maybe some kind of coercion on the RHS can be used here...

theorem toLinfty_mul {f g : α → E} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    (hf.mul hg).toLp (f * g) = hf.toLp f * hg.toLp g :=
  rfl

/- How should one define an HMul on Linfty? Should we be able to get a multiplication on equivalence
classes of measurable functions, even? This would be the right level of generality...in that we
then only would need to provide a proof of essential boundedness of the product. -/

end Memℒp

section Instances

variable {A : Type*} [CStarAlgebra A] [WStarAlgebra A] (a : A) (μ : MeasureTheory.Measure (spectrum ℂ a))

#check Lp ℂ 1 μ

#check Lp ℂ ⊤ μ

#check (Lp ℂ ⊤ μ).add

#check Add (Lp ℂ ⊤ μ)

#exit

-- Is there a ring structure on the essentially bounded functions?
instance Linfty_Ring : Ring (Lp ℂ ⊤ μ) where
  add := (Lp ℂ ⊤ μ).add.add
  add_assoc := add_assoc
  zero := (Lp ℂ ⊤ μ).zero.zero
  zero_add := zero_add
  add_zero := add_zero
  nsmul := sorry
  add_comm := add_comm
  mul f g := by
    simp [eLpNorm_congr_ae AEEqFun.coeFn_mul f g]
    sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  neg := sorry
  zsmul := sorry
  neg_add_cancel := neg_add_cancel

--Maybe get this running and then try to define instances to get L∞ to be a Ring, StarRing, etc...
end Instances

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
