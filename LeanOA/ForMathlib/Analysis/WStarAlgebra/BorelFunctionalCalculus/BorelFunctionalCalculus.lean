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

/- Ok, so Jireh has made a nice HMul instance for Holder conjugate measurable functions. It's involved. I'd still like to make the
`L∞` classes into a `CStarAlgebra`. It's probably a good idea to try. What is the right way forward, here?

Ok. The obvious way forward is exactly the same as for paper math. We look at what is needed for the `CStarAlgebra` declaration.

I can try to rebuild from the ground up, and introduce things from below as needed.

-/

--namespace Linfty

namespace MeasureTheory

variable {α R : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing R] [NormOneClass R]

/-
#synth AddCommGroup (Lp R ⊤ μ)
#synth Norm (Lp R ⊤ μ)
#synth MetricSpace (Lp R ⊤ μ)
#synth HMul (Lp R ⊤ μ)
#synth SMul (Lp R ⊤ μ)
#synth MulOneClass (Lp R ⊤ μ)
#synth Semigroup (Lp R ⊤ μ)
#synth NonAssocSemiring (Lp R ⊤ μ)
#synth NonUnitalSemiring (Lp R ⊤ μ)
#synth Monoid (Lp R ⊤ μ)
#synth MonoidWithZero (Lp R ⊤ μ)
#synth Semiring (Lp R ⊤ μ)
#synth AddGroupWithOne (Lp R ⊤ μ)
-/

--#synth ENNReal.HolderTriple ⊤ ⊤ ⊤
--#synth HSMul (Lp R ⊤ μ) (Lp R ⊤ μ) (Lp R ⊤ μ)

noncomputable instance Linfty.instHMul : HMul (Lp R ⊤ μ) (Lp R ⊤ μ) (Lp R ⊤ μ) where
  hMul f g := f • g

noncomputable instance Linfty.instMul : Mul (Lp R ⊤ μ) where
  mul f g := f * g

instance Linfty.instOne : One (Lp R ⊤ μ) where
  one := ⟨by one(R →ₘ[μ] R) , by sorry⟩

noncomputable instance Linfty.instMulOneClass : MulOneClass (Lp R ⊤ μ) where
  one := sorry
  one_mul := sorry
  mul_one := sorry


#exit
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
