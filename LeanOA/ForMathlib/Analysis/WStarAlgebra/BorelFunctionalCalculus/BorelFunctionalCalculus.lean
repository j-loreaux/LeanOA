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
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Borel Functional Calculus Class

We develop the basic definition of the `BorelFunctionalCalculus` class, imitating
`ContinuousFunctionalCalculus`

## Main declarations

+ TBD

# TODO

-/


namespace BorelSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def support (μ : MeasureTheory.Measure X) : Set X := {x : X | ∀ U ∈ nhds x, μ (interior U) > 0}

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

def ess_range (μ : MeasureTheory.Measure X) (f : X → Y) : Set Y :=
  support (MeasureTheory.Measure.map f μ)

end BorelSpace

namespace MeasureTheory

section LpArithmetic

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology MeasureTheory Uniformity symmDiff

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-Since we are having difficulties with the general construction, let's just try to prove a theorem
saying that if one looks at the a.e. class of the product of two essentially bounded functions,
then the resulting function is also essentially bounded. We then can move on to see how to best say this
with instances, etc.-/

theorem Memℒp.infty_mul {f g : α → ℂ} (hf : Memℒp f ⊤ μ) (hg : Memℒp g ⊤ μ) : Memℒp (f * g) ⊤ μ :=
  ⟨ MeasureTheory.AEStronglyMeasurable.mul (aestronglyMeasurable hf) (aestronglyMeasurable hg),
   by simp only [eLpNorm, ENNReal.top_ne_zero, ↓reduceIte, eLpNormEssSup, Pi.mul_apply, nnnorm_mul, ENNReal.coe_mul]
      exact LE.le.trans_lt (ENNReal.essSup_mul_le (fun x ↦ ‖f x‖₊) (fun x ↦ ‖g x‖₊)) (WithTop.mul_lt_top hf.2 hg.2) ⟩

--Now we have to use the above to develop a `toLp_infty_mul` result.

instance LinftyMul : Mul (Lp ℂ ⊤ μ) where
  mul {f g}:= sorry
  --simp [eLpNorm_congr_ae AEEqFun.coeFn_mul f g]

theorem toLinfty_mul {f g : α → E} (hf : Memℒp f ⊤ μ) (hg : Memℒp g ⊤ μ) :
    (hf.mul hg).toLp (f * g) = hf.toLp f * hg.toLp g :=
  rfl

/- How should one define an HMul on Linfty? Should we be able to get a multiplication on equivalence
classes of measurable functions, even? This would be the right level of generality...in that we
then only would need to provide a proof of essential boundedness of the product. -/

end LpArithmetic

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
