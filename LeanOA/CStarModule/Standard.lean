/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import LeanOA.Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section

/-! # The standard C⋆-module

Given a family `E : ι → Type*` of C⋆-modules over a C⋆-algebra `A`, the *standard C⋆-module*
`ℓ²(A, E)` consists of the additive subgroup of `Π i, E i` consisting of those `x : Π i, E i`
such that the sum `∑' i, ⟪x i, x i⟫_A` converges. Note that such convergence is a consequence
of, but not equivalent to, the convergence of `∑' i, ‖x i‖ ^ 2`. Because of the similarity
with `lp` for `p = 2`, we develop the
API in an analogous manner.

`ℓ²(A, E)` is naturally a complete C⋆-module over `A`, with `A`-valued inner product given by
`⟪x, y⟫_A = ∑' i, ⟪x i, y i⟫_A`.

## Main declarations

+ `CStarModule.MemStandard`: The property on `x : Π i, E i` saying that `∑' i, ⟪x i, x i⟫_A`
  converges.
+ `CStarModule.Standard`: The standard C⋆-module `ℓ²(A, E)` which is the additive subgroup
  with carrier `{x : Π i, E i | MemStandard A x}`.
+ `CStarAlgebra.dominated_convergence`: If `x y : ι → A` are sequences of nonnegative elements
  with `x` summable and `y` dominated by `x`, then `y` is also summable.
+ `CStarModule.Standard.inst`: The standard C⋆-module `ℓ²(A, E)` is a C⋆-module over `A`.
+ `CStarModule.Standard.instCompleteSpace`: The standard C⋆-module `ℓ²(A, E)` is a complete space.
-/

open scoped InnerProductSpace

namespace CStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable {ι : Type*} {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, SMul A (E i)]
variable [∀ i, CStarModule A (E i)]

variable (A) in
/-- The property that for `x : Π i, E i`, the sum `∑' i, ⟪x i, x i⟫_A` converges.

Note: the condition that `∑' i, ⟪x i, x i⟫_A` converges is in general *strictly weaker* than
the condition `∑' i, ‖x i‖ ^ 2` converges. -/
def MemStandard (x : Π i, E i) : Prop := Summable fun i ↦ ⟪x i, x i⟫_A

lemma MemStandard.subtype {x : Π i, E i} (hx : MemStandard A x) (s : Set ι) :
    MemStandard A (fun i : s ↦ x i) := by
  simpa [Function.comp_def] using Summable.subtype hx s

lemma MemStandard.of_memℓp {x : Π i, E i} (hx : Memℓp (‖x ·‖) 2) :
    MemStandard A x :=
  Summable.of_norm <| by simpa [← norm_sq_eq, memℓp_gen_iff] using hx

lemma MemStandard.zero : MemStandard A (0 : Π i, E i) := by
  simp [MemStandard]

lemma MemStandard.neg {x : Π i, E i} (hx : MemStandard A x) :
    MemStandard A (-x) := by
  simpa [MemStandard]

lemma MemStandard.complex_smul (z : ℂ) {x : Π i, E i} (hx : MemStandard A x) :
    MemStandard A (z • x) := by
  simpa [MemStandard] using (hx.const_smul _).const_smul _

lemma MemStandard.smul (a : A) {x : Π i, E i} (hx : MemStandard A x) :
    MemStandard A (a • x) := by
  simpa [MemStandard] using hx.mul_right (star a) |>.mul_left a

open Bornology in
lemma MemStandard.isBounded_norm {x : Π i, E i} (hx : MemStandard A x) :
    IsBounded (Set.range (‖x ·‖ ^ 2)) := by
  rw [MemStandard] at hx
  have := Metric.isBounded_range_of_tendsto_cofinite hx.tendsto_cofinite_zero
  rw [isBounded_iff_forall_norm_le] at this ⊢
  peel this with C _
  rintro - ⟨i, rfl⟩
  specialize this _ ⟨i, rfl⟩
  simpa [norm_sq_eq A]

variable [StarOrderedRing A]

lemma MemStandard.add {x y : Π i, E i} (hx : MemStandard A x) (hy : MemStandard A y) :
    MemStandard A (x + y) := by
  rw [MemStandard] at hx hy ⊢
  refine CStarAlgebra.dominated_convergence ((hx.add hy).add (hx.add hy))
    (fun _ ↦ inner_self_nonneg) fun i ↦ ?_
  calc
    _ ≤ ⟪(x + y) i, (x + y) i⟫_A + ⟪(x - y) i, (x - y) i⟫_A :=
      le_add_of_nonneg_right inner_self_nonneg
    _ = _ := by simp; abel

lemma MemStandard.sub {x y : Π i, E i} (hx : MemStandard A x) (hy : MemStandard A y) :
    MemStandard A (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

lemma MemStandard.summable_inner {x y : Π i, E i} (hx : MemStandard A x) (hy : MemStandard A y) :
    Summable fun i ↦ ⟪x i, y i⟫_A := by
  conv in ⟪x _, y _⟫_A => rw [polarization']
  apply_rules (config := { transparency := .reducible })
    [Summable.const_smul, Summable.add, Summable.sub]
  · exact hy.add hx
  · exact hy.sub hx
  · exact hy.add (hx.complex_smul _)
  · exact hy.sub (hx.complex_smul _)

variable (A E) in
/-- The standard C⋆-module. -/
def Standard : Type _ :=
  { carrier := {x | MemStandard A x}
    zero_mem' := .zero
    add_mem' := .add
    smul_mem' := .complex_smul : Submodule ℂ (Π i, E i) }

@[inherit_doc]
scoped[CStarAlgebra] notation "ℓ²(" A ", " E ")" => CStarModule.Standard A E

open scoped CStarAlgebra

namespace Standard

/-- Create a term of `ℓ²(A, E)` from an `x : Π i, E i` and a proof `hx : MemStandard x`.

Note, because `ℓ²(A, E)` is defeq to the subtype `{x : Π i, E i // MemStandard x}`, Lean
will accept anonymous constructor syntax `⟨x, hx⟩ : ℓ²(A, E)`, but this is defeq abuse,
and can make it hard to work with the resulting term. Instead, users should be prefer
to use this bespoke `Standard.mk` function. -/
def mk (x : Π i, E i) (hx : MemStandard A x) : ℓ²(A, E) := ⟨x, hx⟩

/-- The map from `ℓ²(A, E)` to `Π i, E i`. -/
@[coe]
def toPi (x : ℓ²(A, E)) : Π i, E i := Subtype.val x

instance : DFunLike ℓ²(A, E) ι (fun i ↦ E i) where
  coe := Standard.toPi
  coe_injective' := Subtype.val_injective

@[ext] lemma ext {x y : ℓ²(A, E)} (h : ∀ i, x i = y i) : x = y := DFunLike.ext _ _ h

@[simp] lemma coe_mk {x : Π i, E i} (hx : MemStandard A x) : ⇑(mk x hx) = x := rfl

instance : AddCommGroup ℓ²(A, E) := Submodule.addCommGroup _

instance : Module ℂ ℓ²(A, E) := Submodule.module _

instance : SMul A ℓ²(A, E) where
  smul a x := ⟨_, x.property.smul a⟩

@[simp] lemma memStandard (x : ℓ²(A, E)) : MemStandard A ⇑x := x.property
@[simp] lemma coe_zero : ⇑(0 : ℓ²(A, E)) = (0 : Π i, E i) := rfl
@[simp] lemma coe_add {x y : ℓ²(A, E)} : ⇑(x + y) = (x + y : Π i, E i) := rfl
@[simp] lemma coe_neg {x : ℓ²(A, E)} : ⇑(-x) = (-x : Π i, E i) := rfl
@[simp] lemma coe_sub {x y : ℓ²(A, E)} : ⇑(x - y) = (x - y : Π i, E i) := rfl
@[simp] lemma coe_smul {c : ℂ} {x : ℓ²(A, E)} : ⇑(c • x) = (c • x : Π i, E i) := rfl
@[simp] lemma coe_nsmul {n : ℕ} {x : ℓ²(A, E)} : ⇑(n • x) = (n • x : Π i, E i) := rfl
@[simp] lemma coe_zsmul {n : ℤ} {x : ℓ²(A, E)} : ⇑(n • x) = (n • x : Π i, E i) := rfl
@[simp] lemma coe_smul_right {a : A} {x : ℓ²(A, E)} : ⇑(a • x) = (a • x : Π i, E i) := rfl

noncomputable instance : Norm ℓ²(A, E) where
  norm x := √‖∑' i, ⟪x i, x i⟫_A‖

lemma norm_def {x : ℓ²(A, E)} : ‖x‖ = √‖∑' i, ⟪x i, x i⟫_A‖ := rfl

lemma summable_inner (x y : ℓ²(A, E)) : Summable fun i ↦ ⟪x i, y i⟫_A :=
  x.memStandard.summable_inner y.memStandard

noncomputable instance : Inner A ℓ²(A, E) where
  inner x y := ∑' i, ⟪x i, y i⟫_A

lemma inner_def {x y : ℓ²(A, E)} : ⟪x, y⟫_A = ∑' i, ⟪x i, y i⟫_A := rfl

lemma inner_apply_self_le_inner (x : ℓ²(A, E)) (i : ι) : ⟪x i, x i⟫_A ≤ ⟪x, x⟫_A :=
  x.memStandard.le_tsum _ fun _ _ ↦ inner_self_nonneg

lemma sum_inner_apply_self_le_inner (x : ℓ²(A, E)) (s : Finset ι) :
    ∑ i ∈ s, ⟪x i, x i⟫_A ≤ ⟪x, x⟫_A :=
  x.memStandard.sum_le_tsum s (fun _ _ ↦ inner_self_nonneg)

lemma tsum_inner_apply_self_le_inner (x : ℓ²(A, E)) (s : Set ι) :
    ∑' i : s, ⟪x i, x i⟫_A ≤ ⟪x, x⟫_A :=
  x.memStandard.tsum_subtype_le _ _ (fun _ ↦ inner_self_nonneg)

noncomputable instance : CStarModule A ℓ²(A, E) where
  inner_add_right {x y z} := by
    simpa [inner_def] using (x.summable_inner y).tsum_add (x.summable_inner z)
  inner_self_nonneg := tsum_nonneg fun i => inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun hx ↦ ?_, fun h ↦ by simp [h, inner_def]⟩
    ext i
    rw [coe_zero, Pi.zero_apply, ← inner_self (A := A)]
    exact le_antisymm (hx ▸ inner_apply_self_le_inner x i) inner_self_nonneg
  inner_op_smul_right {a x y} := by
    simpa only [coe_smul_right, Pi.smul_apply, inner_op_smul_right, inner_def]
      using x.summable_inner y |>.tsum_mul_left a
  inner_smul_right_complex {c x y} := by
    simpa only [coe_smul, Pi.smul_apply, inner_smul_right_complex, inner_def]
      using x.summable_inner y |>.tsum_const_smul c
  star_inner x y := by simpa using (starL ℂ).map_tsum (f := fun i ↦ ⟪x i, y i⟫_A)
  norm_eq_sqrt_norm_inner_self _ := rfl

noncomputable instance : NormedAddCommGroup ℓ²(A, E) := normedAddCommGroup A

noncomputable instance : NormedSpace ℂ ℓ²(A, E) := .ofCore <| normedSpaceCore A

lemma norm_apply_le (x : ℓ²(A, E)) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_sq_eq A]
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg (inner_apply_self_le_inner x i)

lemma norm_sum_inner_apply_le (x : ℓ²(A, E)) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪x i, x i⟫_A‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_def, Real.sq_sqrt (by positivity)]
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (s.sum_nonneg fun _ _ ↦ inner_self_nonneg)
    (sum_inner_apply_self_le_inner x s)

/-- The coercion from `ℓ²(A, E)` to `Π i, E i` is uniformly continuous. -/
theorem uniformContinuous_coe :
    UniformContinuous ((↑) : ℓ²(A, E) → Π i, E i) := by
  rw [uniformContinuous_pi]
  intro i
  rw [NormedAddCommGroup.uniformity_basis_dist.uniformContinuous_iff
    NormedAddCommGroup.uniformity_basis_dist]
  refine fun ε hε ↦ ⟨ε, hε, fun f g (hfg : ‖f - g‖ < ε) ↦ ?_⟩
  exact norm_apply_le (f - g) i |>.trans_lt hfg

open Filter Topology

theorem tendsto_of_tendsto_pi {F : ℕ → ℓ²(A, E)} (hF : CauchySeq F) {f : ℓ²(A, E)}
    (hf : Tendsto (fun i ↦ ⇑(F i)) atTop (𝓝 f)) : Tendsto F atTop (𝓝 f) := by
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  have hε' : { p : ℓ²(A, E) × ℓ²(A, E) | ‖p.1 - p.2‖ < ε / √2 } ∈ uniformity ℓ²(A, E) :=
    NormedAddCommGroup.uniformity_basis_dist.mem_of_mem (by positivity)
  refine (hF.eventually_eventually hε').mono ?_
  rintro n (hn : ∀ᶠ l in atTop, ‖F n - F l‖ < ε / √2)
  simp only [Metric.mem_closedBall, dist_eq_norm, norm_def, Real.sqrt_le_iff, hε.le, true_and]
  obtain ⟨s, hs⟩ := (F n - f).memStandard.tsum_vanishing <|
    Metric.ball_mem_nhds 0 (by positivity : 0 < ε ^ 2 / 2)
  rw [← (F n - f).memStandard.sum_add_tsum_compl (s := s) , ← add_halves (ε ^ 2)]
  apply norm_add_le _ _ |>.trans ?_
  gcongr
  · apply le_of_tendsto (f := fun l ↦ ‖∑ x ∈ s, ⟪(F n - F l) x, (F n - F l) x⟫_A‖) (x := atTop)
    · refine tendsto_norm.comp <| tendsto_finset_sum s fun i hi ↦ ?_
      rw [tendsto_pi_nhds] at hf
      have := tendsto_const_nhds (x := F n i) |>.sub (hf i)
      refine (continuous_inner.tendsto _).comp (this.prodMk_nhds this)
    · filter_upwards [hn] with m hm
      rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_lt (by positivity) (by positivity)] at hm
      refine norm_sum_inner_apply_le _ s |>.trans hm.le |>.trans <| by simp [div_pow]
  · simp only [Metric.mem_ball, dist_zero_right] at hs
    exact (hs _ disjoint_compl_left).le

instance instCompletSpace [∀ i, CompleteSpace (E i)] : CompleteSpace ℓ²(A, E) :=
  Metric.complete_of_cauchySeq_tendsto <| by
    intro x hx
    -- A Cauchy sequence in `ℓ²(A, E)` is pointwise convergent; let `y` be the pointwise limit.
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
      (uniformContinuous_coe.comp_cauchySeq hx)
    -- Since the Cauchy sequence is bounded, its pointwise limit `y` is in `ℓ²(A, E)`.
    have hy' : MemStandard A y := by
      rw [MemStandard, summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]
      intro ε hε
      rw [NormedAddCommGroup.cauchySeq_iff] at hx
      have hε8 : 0 < ε / 8 := by positivity
      specialize hx √(ε / 8) (by positivity)
      obtain ⟨N, hN⟩ := hx
      have hxN := (x N).memStandard
      rw [MemStandard, summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm] at hxN
      peel hxN (ε / 8) hε8 with s t ht hxN
      simp only [Function.comp_def, tendsto_pi_nhds] at hy
      refine lt_of_le_of_lt ?_ (half_lt_self hε)
      refine le_of_tendsto (f := fun n ↦ ‖∑ i ∈ t, ⟪x n i, x n i⟫_A‖) (x := atTop) ?_ ?_
      · exact tendsto_norm.comp <| tendsto_finset_sum t fun i hi ↦
          (continuous_inner.tendsto _).comp ((hy i).prodMk_nhds (hy i))
      · filter_upwards [Ici_mem_atTop N] with m hm
        replace hN := norm_neg_add (x N) (x m) ▸ (hN N le_rfl m hm).le
        have (j : ι) (a b : E j) :
            ⟪b, b⟫_A = ⟪a - b, a - b⟫_A + ⟪a, b - a⟫_A + ⟪b - a, a⟫_A + ⟪a, a⟫_A := by
          simp; abel
        conv =>
          enter [1, 1, 2, i]
          rw [this i (x N i) (x m i)]
          simp only [← Pi.sub_apply]
        simp only [Finset.sum_add_distrib]
        have h₁ : ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A‖ ≤ ε / 8 := by
          refine norm_sum_inner_apply_le (x N - x m) t |>.trans ?_
          exact Real.le_sqrt (by positivity) (by positivity) |>.mp hN
        have h₂ : ‖∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A‖ ≤ ε / 8 := by
          classical
          let x' : ℓ²(A, E) := mk (fun i ↦ if i ∈ t then x N i else 0) <| by
            refine (MemStandard.zero (E := E)).congr_cofinite ?_
            filter_upwards [show (tᶜ : Set ι) ∈ cofinite by simp] with i (hi : i ∉ t)
            simp [hi]
          calc
            _ ≤ ‖x'‖ * ‖x m - x N‖ := by
              refine le_of_eq_of_le ?_ (norm_inner_le (A := A) ℓ²(A, E))
              rw [inner_def, tsum_eq_sum fun i (hi : i ∉ t) ↦ by simp [x', hi]]
              congr! 3 with i hi
              simp [x', hi]
            _ ≤ ε / 8 := by
              rw [← Real.mul_self_sqrt hε8.le]
              refine mul_le_mul ?_ (by rwa [← norm_neg, neg_sub]) (by positivity) (by positivity)
              simp only [x', norm_def]
              convert Real.sqrt_le_sqrt hxN.le using 3
              rw [tsum_eq_sum fun i (hi : i ∉ t) ↦ by simp [hi]]
              congr! 2 with i hi
              all_goals simp [hi]
        -- ooh, we *really* want the `setm` tactic below, that would be *sooo* much nicer
        calc
          ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A + ∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A +
              ∑ i ∈ t, ⟪(x m - x N) i, x N i⟫_A + ∑ i ∈ t, ⟪x N i, x N i⟫_A‖
            ≤ ‖∑ i ∈ t, ⟪(x N - x m) i, (x N - x m) i⟫_A‖ + ‖∑ i ∈ t, ⟪x N i, (x m - x N) i⟫_A‖ +
                ‖∑ i ∈ t, ⟪(x m - x N) i, x N i⟫_A‖ + ‖∑ i ∈ t, ⟪x N i, x N i⟫_A‖ :=
            norm_add_le _ _ |>.trans <| add_le_add_left norm_add₃_le _
          _ ≤ ε / 8 + ε / 8 + ε / 8 + ε / 8 := by
            gcongr
            rw [← norm_star, star_sum]
            simpa only [star_inner]
          _ = ε / 2 := by ring
    exact ⟨⟨y, hy'⟩, tendsto_of_tendsto_pi hx hy⟩

end Standard

end CStarModule
