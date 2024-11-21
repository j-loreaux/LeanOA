import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace

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
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, SMul Aᵐᵒᵖ (E i)]
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

lemma MemStandard.smul {x : Π i, E i} (hx : MemStandard x) (z : ℂ) :
    MemStandard (z • x) := by
  simpa [MemStandard] using (hx.const_smul _).const_smul _

open scoped RightActions

lemma MemStandard.smul_right {x : Π i, E i} (hx : MemStandard x) (a : A) :
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

end CStarModule
