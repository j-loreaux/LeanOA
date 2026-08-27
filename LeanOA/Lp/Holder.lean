module

public import LeanOA.Mathlib.Misc
public import LeanOA.Lp.lpSpace

@[expose] public section

open scoped lp ENNReal NNReal

variable {ι 𝕜 : Type*} {E F G : ι → Type*} [RCLike 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]

open ENNReal

variable {p q : ℝ≥0∞} (r : ℝ≥0∞) [hpqr : p.HolderTriple q r]

-- we could take `B` to be a bundled `lp (fun i ↦ E i →L[𝕜] F i →L[𝕜] G i) ∞`, but this has
-- downsides. For example, we would then have to bundle `fun i ↦ (B i).flip`. Moreover, if you
-- have such a bundling, it is relatively easy to apply this lemma.
-- ≤ ‖B‖ * ‖e‖_p * ‖f‖_q
theorem Memℓp.of_bilin_of_top_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e ∞) (hf : Memℓp f q) :
    Memℓp (fun i ↦ B i (e i) (f i)) q := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact Memℓp.all _ -- this result should move to the other file
  obtain ⟨C, hC⟩ := by
    simpa [memℓp_infty_iff, BddAbove, Set.Nonempty, Set.range, upperBounds] using he
  refine .of_norm <| hf.norm.const_mul (K * C) |>.mono fun i ↦ ?_
  simp only [Real.norm_eq_abs]
  have hC_nonneg : 0 ≤ C := norm_nonneg _ |>.trans <| hC (Classical.arbitrary ι)
  replace hK_nonneg : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  rw [abs_of_nonneg (by positivity)]
  calc
    ‖B i (e i) (f i)‖ ≤ ‖B i‖ * ‖e i‖ * ‖f i‖ := (B i (e i)).le_of_opNorm_le ((B i).le_opNorm _) _
    _ ≤ K * C * ‖f i‖ := by gcongr; exacts [hBK i, hC i]

theorem Memℓp.of_bilin_of_top_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) {e : Π i, E i} {f : Π i, F i}
    (he : Memℓp e p) (hf : Memℓp f ∞) :
    Memℓp (fun i ↦ B i (e i) (f i)) p :=
  hf.of_bilin_of_top_left (fun i ↦ (B i).flip) (by simpa using hBK) he

theorem Memℓp.of_bilin_of_zero_left (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (he : Memℓp e 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 := by
  rw [memℓp_zero_iff] at he ⊢
  apply he.subset
  rw [← Set.compl_subset_compl, Set.compl_setOf, Set.compl_setOf]
  simp +contextual

theorem Memℓp.of_bilin_of_zero_right (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {e : Π i, E i} {f : Π i, F i} (hf : Memℓp f 0) :
    Memℓp (fun i ↦ B i (e i) (f i)) 0 :=
  hf.of_bilin_of_zero_left (fun i ↦ (B i).flip)

theorem Real.inner_Lr_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  have := hpqr.holderConjugate_div_div
  have hp := hpqr.pos
  have hq := hpqr.symm.pos
  have hr := hpqr.pos'
  calc ∑ i ∈ s, (f i * g i) ^ r
    _ = ∑ i ∈ s, (f i) ^ r * (g i) ^ r := by
      refine s.sum_congr rfl fun i hi ↦ ?_
      rw [mul_rpow (hf i hi) (hg i hi)]
    _ ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
      apply Real.inner_le_Lp_mul_Lq_of_nonneg s this (fun i hi ↦ Real.rpow_nonneg (hf i hi) _)
        (fun i hi ↦ Real.rpow_nonneg (hg i hi) _) |>.trans_eq
      congr! 2
      all_goals try simp only [fieldEq]
      all_goals
        refine s.sum_congr rfl fun i hi ↦ ?_
        rw [← Real.rpow_mul (by grind)]
        grind

lemma Memℓp.holder_top_left_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hCe : ∀ i, ‖e i‖ ≤ C) (hKe : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ q.toReal ≤ (K * C) ^ q.toReal * D := by
  grw [← hKe s, s.mul_sum]
  apply s.sum_le_sum fun i hi ↦ ?_
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le_of_le (hBK i) (hCe i)) _

lemma Memℓp.holder_top_right_bound
    {e : (i : ι) → E i} {f : (i : ι) → F i} (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i)
    {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C) (hDf : ∀ i, ‖f i‖ ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ p.toReal ≤ (K * D) ^ p.toReal * C :=
  Memℓp.holder_top_left_bound (B · |>.flip) (by simpa) hK hD hDf hCe s

lemma Memℓp.holder_gen_bound {e : (i : ι) → E i} {f : (i : ι) → F i}
    (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K C D : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hCe : ∀ s, ∑ i ∈ s, ‖e i‖ ^ p.toReal ≤ C)
    (hDf : ∀ s, ∑ i ∈ s, ‖f i‖ ^ q.toReal ≤ D) (s : Finset ι) :
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal ≤
      K ^ r.toReal * C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) := by
  have hpqr := hpqr.toReal r hp hq
  have hr := hpqr.pos'
  suffices ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal ≤
      C ^ (r.toReal / p.toReal) * D ^ (r.toReal / q.toReal) from calc
    ∑ i ∈ s, ‖B i (e i) (f i)‖ ^ r.toReal
    _ ≤ K ^ r.toReal * ∑ i ∈ s, (‖e i‖ * ‖f i‖) ^ r.toReal := by
      rw [s.mul_sum]
      gcongr with i hi
      rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_assoc]
      gcongr
      exact (B i (e i)).le_of_opNorm_le ((B i).le_of_opNorm_le (hBK i) _) _
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
  calc
    _ ≤ (∑ i ∈ s, ‖e i‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
        (∑ i ∈ s, ‖f i‖ ^ q.toReal) ^ (r.toReal / q.toReal) := by
      apply Real.inner_Lr_le_Lp_mul_Lq_of_nonneg s hpqr <;> (intros; positivity)
    _ ≤ _ := by
      gcongr
      · exact hCe s
      · exact hDf s

lemma Memℓp.holder {e : (i : ι) → E i} {f : (i : ι) → F i} (he : Memℓp e p) (hf : Memℓp f q)
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K) :
    Memℓp (fun i ↦ B i (e i) (f i)) r := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · exact Memℓp.all _ -- this result should move to the other file
  have hK : 0 ≤ K := norm_nonneg (B (Classical.arbitrary ι)) |>.trans <| hBK _
  have hpqr' := hpqr.inv_eq
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_all only [ENNReal.inv_zero, top_add, inv_eq_top]
    exact he.of_bilin_of_zero_left B
  · simp_all only [inv_top, zero_add, inv_inj]
    exact he.of_bilin_of_top_left B hBK hf
  obtain (rfl | rfl | hq) := q.trichotomy
  · simp_all only [ENNReal.inv_zero, add_top, inv_eq_top]
    exact hf.of_bilin_of_zero_right B
  · simp_all only [inv_top, add_zero, inv_inj]
    exact he.of_bilin_of_top_right B hBK hf
  obtain ⟨C, hC, hCe⟩ := memℓp_gen_iff'' hp |>.mp he
  obtain ⟨D, hD, hDf⟩ := memℓp_gen_iff'' hq |>.mp hf
  exact memℓp_gen' <| Memℓp.holder_gen_bound r hp hq B hBK hK hC hCe hDf

/-- The map between `lp` spaces satisfying `ENNReal.HolderTriple` induced by a
uniformly bounded family of continuous bilinear maps on the underlying spaces. -/
@[simps]
def lp.holder (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    lp G r where
  val := fun i ↦ B i (e i) (f i)
  property := (lp.memℓp e).holder _ (lp.memℓp f) B hBK

set_option backward.isDefEq.respectTransparency false in
/-- `lp.holder` as a bilinear map. -/
@[simps!]
noncomputable def lp.holderₗ (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ}
    (hBK : ∀ i, ‖B i‖ ≤ K) : lp E p →ₗ[𝕜] lp F q →ₗ[𝕜] lp G r :=
  .mk₂ 𝕜 (lp.holder r B hBK) ?_ ?_ ?_ ?_
where finally
  all_goals intros; ext; simp

/-- `lp.holder` as a continuous bilinear map. -/
noncomputable def lp.holderL [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] lp G r :=
  lp.holderₗ r B hBK |>.mkContinuous₂ K fun e f ↦ by
    obtain ⟨(rfl | hp), (rfl | hq)⟩ := And.intro p.dichotomy q.dichotomy
    · obtain rfl : r = ⊤ := ENNReal.HolderTriple.unique ∞ ∞ r ∞
      refine lp.norm_le_of_forall_le (by positivity) fun i ↦ ?_
      refine (B i).le_of_opNorm₂_le_of_le (hBK i) ?_ ?_
      all_goals exact lp.norm_apply_le_norm (by simp) ..
    · obtain rfl : r = q := ENNReal.HolderTriple.unique ∞ q r q
      refine lp.norm_le_of_forall_sum_le (zero_lt_one.trans_le hq) (by positivity) fun s ↦ ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_left_bound B hBK
        (by positivity) (by positivity) (lp.norm_apply_le_norm (by simp) _) ?_ s
      exact lp.sum_rpow_le_norm_rpow (zero_lt_one.trans_le hq) f
    · obtain rfl : r = p := ENNReal.HolderTriple.unique p ∞ r p
      refine lp.norm_le_of_forall_sum_le (zero_lt_one.trans_le hp) (by positivity) fun s ↦ ?_
      rw [mul_right_comm, Real.mul_rpow (by positivity) (by positivity)]
      refine Memℓp.holder_top_right_bound B hBK
        (by positivity) (by positivity) ?_ (lp.norm_apply_le_norm (by simp) _) s
      exact lp.sum_rpow_le_norm_rpow (zero_lt_one.trans_le hp) e
    · have hpqr := hpqr.toReal r (zero_lt_one.trans_le hp) (zero_lt_one.trans_le hq)
      have hp := hpqr.pos
      have hq := hpqr.symm.pos
      refine lp.norm_le_of_forall_sum_le hpqr.pos' (by positivity) fun s ↦ ?_
      simp only [holderₗ_apply_apply_coe]
      calc
        _ ≤ K ^ r.toReal * (‖e‖ ^ p.toReal) ^ (r.toReal / p.toReal) *
          (‖f‖ ^ q.toReal) ^ (r.toReal / q.toReal) :=
          Memℓp.holder_gen_bound r hp hq B hBK (by positivity) (by positivity)
            (lp.sum_rpow_le_norm_rpow hp e) (lp.sum_rpow_le_norm_rpow hq f) s
        _ ≤ _ := by
          rw [← Real.rpow_mul, ← Real.rpow_mul]
          · simp only [← mul_div_assoc, ne_eq, hp.ne', not_false_eq_true, mul_div_cancel_left₀,
            hq.ne', fieldLe]
            rw [Real.mul_rpow, Real.mul_rpow]
            all_goals positivity
          all_goals positivity

lemma lp.norm_holderL_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖lp.holderL (p := p) (q := q) r B hBK‖ ≤ K :=
  LinearMap.mkContinuous₂_norm_le _ K.2 _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

variable (p q) in
/-- The natural pairing between `lp E p` and `lp F q` (for Hölder conjugate `p q : ℝ≥0∞`) with
values in a space `H` induced by a family of bilinear maps `B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H`.

This is given by `∑' i, B (e i) (f i)`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, which is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is the natural map
`lp (fun _ ↦ StrongDual 𝕜 E) p →L[𝕜] StrongDual 𝕜 (lp E q)`.
-/
noncomputable def lp.dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    lp E p →L[𝕜] lp F q →L[𝕜] H :=
  (lp.tsumCLM 𝕜 ι H |>.postcomp <| lp F q) ∘L (lp.holderL 1 B hBK)

lemma lp.dualPairing_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K)
    (e : lp E p) (f : lp F q) :
    lp.dualPairing p q B hBK e f = ∑' i, B i (e i) (f i) :=
  rfl

lemma lp.norm_dualPairing [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] H) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) :
    ‖lp.dualPairing p q B hBK‖ ≤ K := calc
  ‖lp.dualPairing p q B hBK‖
  _ ≤ ‖(tsumCLM 𝕜 ι H).postcomp (lp F q)‖ * ‖holderL 1 B hBK‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  _ ≤ 1 * K := by
    gcongr
    · exact ContinuousLinearMap.norm_postcomp_le _ |>.trans lp.norm_tsumCLM
    · exact norm_holderL_le 1 B hBK
  _ = K := one_mul _
