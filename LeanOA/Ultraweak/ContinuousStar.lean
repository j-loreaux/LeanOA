module

public import LeanOA.Ultraweak.OrderClosed
public import LeanOA.Ultraweak.Dual
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open scoped NNReal Topology

namespace Ultraweak

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [Predual ℂ M P] [CompleteSpace P]

set_option backward.isDefEq.respectTransparency false in
open Complex in
open scoped Pointwise ComplexStarModule in
instance : ContinuousStar σ(M, P) where
  continuous_star := by
    /- The `ℝ`-linear map `realPart` is a contractive idempotent whose range consists of the
    selfadjoint elements and whose kernel consists of the skewadjoint elements; both are
    ultraweakly closed, so `realPart` is ultraweakly continuous. -/
    let R : σ(M, P) →ₗ[ℝ] σ(M, P) := (selfAdjoint.submodule ℝ σ(M, P)).subtype ∘ₗ realPart
    have hR : Continuous R := by
      refine continuous_of_isIdempotentElem_of_real R ?_ 1 (fun x ↦ ?_) ?_ ?_
      · ext x
        exact (ℜ x).2.coe_realPart
      · rw [one_mul]
        exact realPart.norm_le (ofUltraweak x)
      · convert isClosed_setOf_isSelfAdjoint (M := M) (P := P) using 1
        ext x
        exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (ℜ y).2, fun hx ↦ ⟨x, hx.coe_realPart⟩⟩
      · convert isClosed_setOf_isSelfAdjoint (M := M) (P := P) |>.smul₀ I using 1
        ext x
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Set.mem_smul_set, Set.mem_ofPred_eq]
        refine ⟨fun hx ↦ ⟨ℑ x, (ℑ x).2, ?_⟩, ?_⟩
        · have hx' : (ℜ x : σ(M, P)) = 0 := hx
          simpa [hx'] using realPart_add_I_smul_imaginaryPart x
        · rintro ⟨y, hy, rfl⟩
          change (ℜ (I • y) : σ(M, P)) = 0
          rw [realPart_I_smul, hy.imaginaryPart, neg_zero, ZeroMemClass.coe_zero]
    /- Since `star x = 2 • ℜ x - x`, the result follows. -/
    convert! (hR.const_smul (2 : ℝ)).sub continuous_id using 2
    ext x
    -- `change` is necessary to see through the defeq between `selfAdjoint.submodule ℝ σ(M, P)
    -- and `selfAdjoint σ(M, P)`. To do this correctly, we would need to set up a linear
    -- equivalence between them.
    change star x = (2 : ℝ) • realPart x - x
    simp [realPart_apply_coe, smul_smul]

end Ultraweak
