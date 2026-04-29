import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.LpEquiv

open scoped lp ENNReal
section NonDependent

variable {ι 𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [CompleteSpace E]

lemma lp.norm_tsumCLM {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    ‖lp.tsumCLM 𝕜 ι E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end NonDependent

section Dependent

variable {ι 𝕜 : Type*} {E F : ι → Type*} [NontriviallyNormedField 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
variable {p q r : ℝ≥0∞}

set_option backward.isDefEq.respectTransparency false in
/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space. -/
@[simps!]
noncomputable def lp.mapCLM (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    lp E p →L[𝕜] lp F p :=
  haveI key (i : ι) (x : E i) : ‖T i x‖ ≤ K * ‖x‖ := by
    simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hK]
      using (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i ↦ T i (x i), lp.memℓp x |>.norm.const_mul K |>.mono
        (fun _ ↦ by simpa [abs_of_nonneg hK] using key ..) |>.of_norm⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    K
    fun x ↦ by
      rw [← lp.norm_toNorm]
      conv_rhs => rw [← lp.norm_toNorm, ← abs_of_nonneg hK, ← Real.norm_eq_abs, ← norm_smul]
      apply lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun i ↦ ?_
      simpa [abs_of_nonneg hK] using key ..

lemma lp.norm_mapCLM_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    ‖lp.mapCLM p T hK hTK‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ hK _

end Dependent
