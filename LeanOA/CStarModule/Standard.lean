/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # The standard C⋆-module -/

open scoped InnerProductSpace

namespace CStarModule

section Polarization

variable {E A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule A E]

open Complex

lemma polarization {x y : E} :
    4 • ⟪y, x⟫_A = ⟪x + y, x + y⟫_A - ⟪x - y, x - y⟫_A +
      I • ⟪x + I • y, x + I • y⟫_A - I • ⟪x - I • y, x - I • y⟫_A := by
  simp [smul_smul, smul_sub]
  abel

lemma polarization' {x y : E} :
    ⟪y, x⟫_A = (1 / 4 : ℂ) • (⟪x + y, x + y⟫_A - ⟪x - y, x - y⟫_A +
      I • ⟪x + I • y, x + I • y⟫_A - I • ⟪x - I • y, x - I • y⟫_A) := by
  rw [← (IsUnit.mk0 (4 : ℂ) (by norm_num)).smul_left_cancel, ofNat_smul_eq_nsmul ℂ 4]
  simpa only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, smul_inv_smul₀]
    using CStarModule.polarization

end Polarization

variable {ι : Type*} {E : ι → Type*}
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, SMul Aᵐᵒᵖ (E i)]
variable [∀ i, CStarModule A (E i)]

/-- The property that for `x : Π i, E i`, the sum `∑' i, ⟪x i, x i⟫_A` converges.

Note: the condition that `∑' i, ⟪x i, x i⟫_A` converges is in general *strictly weaker* than
the condition `∑' i, ‖x i‖ ^ 2` converges. -/
def MemStandard (x : Π i, E i) : Prop := Summable fun i ↦ ⟪x i, x i⟫_A

lemma MemStandard.of_memℓp {x : Π i, E i} (hx : Memℓp (‖x ·‖) 2) :
    MemStandard x :=
  Summable.of_norm <| by simpa [← norm_sq_eq, memℓp_gen_iff] using hx

lemma dominated_convergence {x y : ι → A} (hx : Summable x) (hy_nonneg : ∀ i, 0 ≤ y i)
    (h_le : ∀ i, y i ≤ x i) : Summable y := by
  rw [summable_iff_vanishing] at hx ⊢
  intro u hu
  obtain ⟨ε, ε_pos, hε⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hu
  specialize hx (Metric.closedBall 0 ε) (Metric.closedBall_mem_nhds 0 ε_pos)
  peel hx with s t hst _
  refine hε ?_
  simp only [Metric.mem_closedBall, dist_zero_right] at this ⊢
  refine le_trans ?_ this
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (t.sum_nonneg fun i _ ↦ (hy_nonneg i)) ?_
  gcongr
  exact h_le _

lemma MemStandard.zero : MemStandard (0 : Π i, E i) := by
  simpa [MemStandard] using summable_zero

lemma MemStandard.add {x y : Π i, E i} (hx : MemStandard x) (hy : MemStandard y) :
    MemStandard (x + y) := by
  rw [MemStandard] at hx hy ⊢
  refine dominated_convergence ((hx.add hy).add (hx.add hy)) (fun _ ↦ inner_self_nonneg) fun i ↦ ?_
  calc
    _ ≤ ⟪(x + y) i, (x + y) i⟫_A + ⟪(x - y) i, (x - y) i⟫_A :=
      le_add_of_nonneg_right inner_self_nonneg
    _ = _ := by simp; abel

lemma MemStandard.neg {x : Π i, E i} (hx : MemStandard x) :
    MemStandard (-x) := by
  simpa [MemStandard]

lemma MemStandard.sub {x y : Π i, E i} (hx : MemStandard x) (hy : MemStandard y) :
    MemStandard (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma MemStandard.smul (z : ℂ) {x : Π i, E i} (hx : MemStandard x) :
    MemStandard (z • x) := by
  simpa [MemStandard] using (hx.const_smul _).const_smul _

open scoped RightActions

lemma MemStandard.smul_right (a : A) {x : Π i, E i} (hx : MemStandard x) :
    MemStandard (x <• a) := by
  simpa [MemStandard] using hx.mul_left (star a) |>.mul_right a

open Bornology in
lemma MemStandard.isBounded_norm {x : Π i, E i} (hx : MemStandard x) :
    IsBounded (Set.range (‖x ·‖ ^ 2)) := by
  rw [MemStandard] at hx
  have := Metric.isBounded_range_of_tendsto_cofinite hx.tendsto_cofinite_zero
  rw [isBounded_iff_forall_norm_le] at this ⊢
  peel this with C _
  rintro - ⟨i, rfl⟩
  specialize this _ ⟨i, rfl⟩
  simpa [norm_sq_eq]

lemma MemStandard.summable_inner {x y : Π i, E i} (hx : MemStandard x) (hy : MemStandard y) :
    Summable fun i ↦ ⟪x i, y i⟫_A := by
  conv in ⟪x _, y _⟫_A => rw [polarization']
  apply_rules (config := { transparency := .reducible }) [Summable.const_smul, Summable.add, Summable.sub]
  · exact hy.add hx
  · exact hy.sub hx
  · exact hy.add (hx.smul _)
  · exact hy.sub (hx.smul _)

variable (E) in
/-- The standard C⋆-module  -/
def Standard : Type _ :=
  { carrier := {x | MemStandard x}
    zero_mem' := .zero
    add_mem' := .add
    smul_mem' := .smul : Submodule ℂ (Π i, E i) }

scoped[CStarAlgebra] notation "ℓ²(" E ")" => CStarModule.Standard E

open scoped CStarAlgebra

namespace Standard

/-- Create a term of `ℓ²(E)` from an `x : Π i, E i` and a proof `hx : MemStandard x`.

Note, because `ℓ²(E)` is defeq to the subtype `{x : Π i, E i /‌/ MemStandard x}`, Lean will accept
anonymous constructor syntax `⟨x, hx⟩ : ℓ²(E)`, but this is defeq abuse, and can make it hard to work
with the resulting term. Instead, users should be prefer to use this bespoke `Standard.mk` function. -/
def mk (x : Π i, E i) (hx : MemStandard x) : ℓ²(E) := ⟨x, hx⟩

/-- The map from `ℓ²(E)` to `Π i, E i`. -/
@[coe]
def toPi (x : ℓ²(E)) : Π i, E i := Subtype.val x

instance : DFunLike ℓ²(E) ι (fun i ↦ E i) where
  coe := Standard.toPi
  coe_injective' := Subtype.val_injective

@[ext] lemma ext {x y : ℓ²(E)} (h : ∀ i, x i = y i) : x = y := DFunLike.ext _ _ h

@[simp] lemma coe_mk {x : Π i, E i} (hx) : ⇑(mk x hx) = x := rfl

instance : AddCommGroup ℓ²(E) := Submodule.addCommGroup _

instance : Module ℂ ℓ²(E) := Submodule.module _

instance : SMul Aᵐᵒᵖ ℓ²(E) where
  smul a x := ⟨_, x.property.smul_right (MulOpposite.unop a)⟩

@[simp] lemma memStandard (x : ℓ²(E)) : MemStandard ⇑x := x.property
@[simp] lemma coe_zero : ⇑(0 : ℓ²(E)) = (0 : Π i, E i) := rfl
@[simp] lemma coe_add {x y : ℓ²(E)} : ⇑(x + y) = (x + y : Π i, E i) := rfl
@[simp] lemma coe_neg {x : ℓ²(E)} : ⇑(-x) = (-x : Π i, E i) := rfl
@[simp] lemma coe_sub {x y : ℓ²(E)} : ⇑(x - y) = (x - y : Π i, E i) := rfl
@[simp] lemma coe_smul {c : ℂ} {x : ℓ²(E)} : ⇑(c • x) = (c • x : Π i, E i) := rfl
@[simp] lemma coe_nsmul {n : ℕ} {x : ℓ²(E)} : ⇑(n • x) = (n • x : Π i, E i) := rfl
@[simp] lemma coe_zsmul {n : ℤ} {x : ℓ²(E)} : ⇑(n • x) = (n • x : Π i, E i) := rfl
@[simp] lemma coe_smul_right {a : A} {x : ℓ²(E)} : ⇑(x <• a) = (x <• a : Π i, E i) := rfl

noncomputable instance : Norm ℓ²(E) where
  norm x := √‖∑' i, ⟪x i, x i⟫_A‖

lemma norm_def {x : ℓ²(E)} : ‖x‖ = √‖∑' i, ⟪x i, x i⟫_A‖ := rfl

lemma summable_inner (x y : ℓ²(E)) : Summable fun i ↦ ⟪x i, y i⟫_A :=
  x.memStandard.summable_inner y.memStandard

noncomputable instance : Inner A ℓ²(E) where
  inner x y := ∑' i, ⟪x i, y i⟫_A

lemma inner_def {x y : ℓ²(E)} : ⟪x, y⟫_A = ∑' i, ⟪x i, y i⟫_A := rfl

lemma inner_apply_self_le_inner (x : ℓ²(E)) (i : ι) : ⟪x i, x i⟫_A ≤ ⟪x, x⟫_A :=
  le_tsum x.memStandard _ fun _ _ ↦ inner_self_nonneg

lemma sum_inner_apply_self_le_inner (x : ℓ²(E)) (s : Finset ι) : ∑ i in s, ⟪x i, x i⟫_A ≤ ⟪x, x⟫_A :=
  sum_le_tsum s (fun _ _ ↦ inner_self_nonneg) x.memStandard

noncomputable instance : CStarModule A ℓ²(E) where
  inner_add_right {x y z} := by
    simpa [inner_def] using tsum_add (x.summable_inner y) (x.summable_inner z)
  inner_self_nonneg := tsum_nonneg fun i => inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun hx ↦ ?_, fun h ↦ by simp [h, inner_def]⟩
    ext i
    rw [coe_zero, Pi.zero_apply, ← inner_self]
    exact le_antisymm (hx ▸ inner_apply_self_le_inner x i) inner_self_nonneg
  inner_op_smul_right {a x y} := by
    simpa only [coe_smul_right, Pi.smul_apply, inner_op_smul_right, inner_def]
      using x.summable_inner y |>.tsum_mul_right a
  inner_smul_right_complex {c x y} := by
    simpa only [coe_smul, Pi.smul_apply, inner_smul_right_complex, inner_def]
      using tsum_const_smul c <| x.summable_inner y
  star_inner x y := by simpa using (starL ℂ).map_tsum (f := fun i ↦ ⟪x i, y i⟫_A)
  norm_eq_sqrt_norm_inner_self _ := rfl

noncomputable instance : NormedAddCommGroup ℓ²(E) := normedAddCommGroup

instance : NormedSpace ℂ ℓ²(E) := .ofCore normedSpaceCore

lemma norm_apply_le (x : ℓ²(E)) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_sq_eq]
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg (inner_apply_self_le_inner x i)

lemma norm_sum_inner_apply_le (x : ℓ²(E)) (s : Finset ι) :
    ‖∑ i in s, ⟪x i, x i⟫_A‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_def, Real.sq_sqrt (by positivity)]
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (s.sum_nonneg fun _ _ ↦ inner_self_nonneg)
    (sum_inner_apply_self_le_inner x s)

/-- The coercion from `ℓ²(E)` to `Π i, E i` is uniformly continuous. -/
theorem uniformContinuous_coe :
    UniformContinuous ((↑) : ℓ²(E) → Π i, E i) := by
  rw [uniformContinuous_pi]
  intro i
  rw [NormedAddCommGroup.uniformity_basis_dist.uniformContinuous_iff
    NormedAddCommGroup.uniformity_basis_dist]
  refine fun ε hε ↦ ⟨ε, hε, fun f g (hfg : ‖f - g‖ < ε) ↦ ?_⟩
  exact norm_apply_le (f - g) i |>.trans_lt hfg

open Filter

instance instCompletSpace [∀ i, CompleteSpace (E i)] : CompleteSpace ℓ²(E) :=
  Metric.complete_of_cauchySeq_tendsto <| by
    intro x hx
    -- A Cauchy sequence in `ℓ²(E)` is pointwise convergent; let `y` be the pointwise limit.
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
      (uniformContinuous_coe.comp_cauchySeq hx)
    -- Since the Cauchy sequence is bounded, its pointwise limit `y` is in `ℓ²(E)`.
    have hy' : MemStandard y := by
      rw [MemStandard, summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]
      intro ε hε
      rw [NormedAddCommGroup.cauchySeq_iff] at hx
      have hε8 : 0 < ε / 8 := by positivity
      specialize hx √(ε / 8) (by positivity)
      obtain ⟨N, hN⟩ := hx
      have hxN := (x N).memStandard
      rw [MemStandard, summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm] at hxN
      specialize hxN (ε / 8) hε8
      obtain ⟨s, hs⟩ := hxN
      use s
      peel hs with t ht hxN
      simp only [Function.comp_def, tendsto_pi_nhds] at hy
      refine lt_of_le_of_lt ?_ (half_lt_self hε)
      refine le_of_tendsto (f := fun n ↦ ‖∑ i ∈ t, ⟪x n i, x n i⟫_A‖) (x := atTop) ?_ ?_
      · exact tendsto_norm.comp <| tendsto_finset_sum t fun i hi ↦
          (continuous_inner.tendsto _).comp ((hy i).prod_mk_nhds (hy i))
      · filter_upwards [Ici_mem_atTop N] with m hm
        replace hN := (hN N le_rfl m hm).le
        have (j : ι) (a b : E j) :
            ⟪b, b⟫_A = ⟪a - b, a - b⟫_A + ⟪a, b - a⟫_A + ⟪b - a, a⟫_A + ⟪a, a⟫_A := by
          simp; abel
        conv =>
          enter [1, 1, 2, i]
          rw [this i (x N i) (x m i)]
          simp only [← Pi.sub_apply]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h₁ : ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A‖ ≤ ε / 8 := by
          refine norm_sum_inner_apply_le (x N - x m) t |>.trans ?_
          exact Real.le_sqrt (by positivity) (by positivity) |>.mp hN
        have h₂ : ‖∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A‖ ≤ ε / 8 := by
          classical
          let x' : ℓ²(E) := mk (fun i ↦ if i ∈ t then x N i else 0) <| by
            refine (MemStandard.zero (E := E)).congr_cofinite ?_
            filter_upwards [show (tᶜ : Set ι) ∈ cofinite by simp] with i (hi : i ∉ t)
            simp [hi]
          calc
            _ ≤ ‖x'‖ * ‖x m - x N‖ := by
              refine le_of_eq_of_le ?_ (norm_inner_le ℓ²(E))
              rw [inner_def, tsum_eq_sum fun i (hi : i ∉ t) ↦ by simp [x', hi]]
              congr! 3 with i hi
              simp [x', hi]
            _ ≤ ε / 8 := by
              rw [← Real.mul_self_sqrt hε8.le]
              refine mul_le_mul ?_ (by rwa [← norm_neg, neg_sub]) (by positivity) (by positivity)
              simp only [x', norm_def]
              convert Real.sqrt_le_sqrt hxN.le using 3
              rw [tsum_eq_sum fun i (hi : i ∉ t) ↦ by simp [x', hi]]
              congr! 2 with i hi
              all_goals simp [hi]
        -- ooh, we *really* want the `setm` tactic below, that would be *sooo* much nicer
        calc
          ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A + ∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A +
              ∑ i ∈ t, ⟪(x m - x N) i, x N i⟫_A + ∑ i ∈ t, ⟪x N i, x N i⟫_A‖
            ≤ ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A‖ + ‖∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A‖ +
                ‖∑ i ∈ t, ⟪(x m - x N) i, x N i⟫_A‖ + ‖∑ i ∈ t, ⟪x N i, x N i⟫_A‖ :=
            norm_add_le _ _ |>.trans <| add_le_add_right norm_add₃_le _
          _ ≤ ε / 8 + ε / 8 + ε / 8 + ε / 8 := by
            gcongr
            rw [← norm_star, star_sum]
            simpa only [star_inner]
          _ = ε / 2 := by ring
      --memℓp_of_tendsto hF.isBounded_range hf
    -- And therefore `f` is its limit in the `ℓ²(E)` topology as well as pointwise.
    -- exact ⟨⟨f, hf'⟩, tendsto_lp_of_tendsto_pi hF hf⟩
    sorry

end Standard

end CStarModule
