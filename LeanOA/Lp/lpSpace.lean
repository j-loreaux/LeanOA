import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.LpEquiv

@[inherit_doc]
scoped [lp] notation "ℓ^" p "(" ι ", " 𝕜 ")" => lp (fun _ : ι ↦ 𝕜) p
@[inherit_doc]
scoped [lp] notation "ℓ¹(" ι ", " 𝕜 ")" => lp (fun _ : ι ↦ 𝕜) 1

open scoped lp ENNReal

section NonDependent

variable {ι 𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

lemma lp.norm_tsum_le (f : ℓ¹(ι, E)) :
    ‖∑' i, f i‖ ≤ ‖f‖ := calc
  ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm (.of_norm (by simpa using f.2.summable))
  _ = ‖f‖ := by simp [lp.norm_eq_tsum_rpow]

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
variable (ι 𝕜 E) in
/-- Summation (i.e., `tsum`) in `lp (fun _ ↦ E) 1` as a linear map. -/
@[simps!]
noncomputable def lp.tsumCLM : ℓ¹(ι, E) →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun f := ∑' i, f i
      map_add' f g := by
        simp only [AddSubgroup.coe_add, Pi.add_apply]
        rw [← Summable.tsum_add]
        exacts [.of_norm (by simpa using f.2.summable), .of_norm (by simpa using g.2.summable)]
      map_smul' c f := by
        simp only [coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        exact Summable.tsum_const_smul _ (.of_norm (by simpa using f.2.summable))  }
    1 (fun f ↦ by simpa using lp.norm_tsum_le f)

lemma lp.norm_tsumCLM {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    ‖lp.tsumCLM ι 𝕜 E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end NonDependent


section Dependent

section NormedRing

variable {ι 𝕜 : Type*} {E F : ι → Type*} [NormedRing 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, IsBoundedSMul 𝕜 (F i)]
variable {p q r : ℝ≥0∞}

theorem memℓp_norm_iff {f : (i : ι) → E i} :
    Memℓp (‖f ·‖) p ↔ Memℓp f p := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp [memℓp_zero_iff]
  · simp [memℓp_infty_iff]
  · simp [memℓp_gen_iff hp]

alias ⟨Memℓp.of_norm, Memℓp.norm⟩ := memℓp_norm_iff

theorem Memℓp.mono {f : (i : ι) → E i} {g : (i : ι) → F i}
    (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ ‖g i‖) :
    Memℓp f p := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_rw [memℓp_zero_iff, ← norm_pos_iff] at hg ⊢
    refine hg.subset fun i hi ↦ hi.trans_le <| hfg i
  · rw [memℓp_infty_iff] at hg ⊢
    exact hg.range_mono _ hfg
  · rw [memℓp_gen_iff hp] at hg ⊢
    apply hg.of_norm_bounded fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact hfg i

theorem memℓp_gen_iff' {f : (i : ι) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∀ (s : Finset ι), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑' i, ‖f i‖ ^ p.toReal := by
  refine ⟨fun hf ↦ ?_, memℓp_gen'⟩
  simpa [upperBounds] using isLUB_hasSum (by intro; positivity) (hf.summable hp |>.hasSum) |>.1

theorem memℓp_gen_iff'' {f : (i : ι) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∃ C, 0 ≤ C ∧ ∀ (s : Finset ι), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C := by
  refine ⟨fun hf ↦ ?_, fun ⟨C, _, hC⟩ ↦ memℓp_gen' hC⟩
  exact ⟨_, tsum_nonneg fun i ↦ (by positivity), memℓp_gen_iff' hp |>.mp hf⟩

lemma Memℓp.summable_of_one {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {x : ι → E}
    (hx : Memℓp x 1) : Summable x :=
  .of_norm <| by simpa using hx.summable

/-- The sequence of norms of a term of `lp E p` as a term of `ℓ^p(ι, ℝ)`. -/
@[simps]
def lp.toNorm {p : ℝ≥0∞} (x : lp E p) : ℓ^p(ι, ℝ) :=
  ⟨fun i ↦ ‖x i‖, lp.memℓp x |>.norm⟩

lemma lp.norm_toNorm {p : ℝ≥0∞} {x : lp E p} :
    ‖lp.toNorm x‖ = ‖x‖ := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp [lp.norm_eq_card_dsupport]
  · simp [lp.norm_eq_ciSup]
  · simp [lp.norm_eq_tsum_rpow hp]

lemma lp.norm_mono {p : ℝ≥0∞} (hp : p ≠ 0)
    {x : lp E p} {y : lp F p} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖x‖ ≤ ‖y‖ := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp at hp
  · exact lp.norm_le_of_forall_le (by positivity)
      fun i ↦(h i).trans <|lp.norm_apply_le_norm hp y i
  · exact lp.norm_le_of_forall_sum_le hp (lp.norm_nonneg' _) fun s ↦ calc
      ∑ i ∈ s, ‖x i‖ ^ p.toReal
      _ ≤ ∑ i ∈ s, ‖y i‖ ^ p.toReal := by gcongr with i _; exact h i
      _ ≤ ‖y‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hp y s

lemma lp.lipschitzWith_one_eval (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) :
    LipschitzWith 1 (fun x : lp E p ↦ x i) :=
  .mk_one fun x y ↦ by
    simp_rw [dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' ..

-- note, probably we should make a bare function version of this too, or just call this one `ofLE`.
variable (E) in
/-- Inclusion map from `lp E p` to `lp E q` for `p ≤ q`, as an additive monoid homomorphism. -/
def lp.addMonoidHomOfLE (h : p ≤ q) :
    lp E p →+ lp E q where
  toFun f := ⟨f.1, lp.memℓp f |>.of_exponent_ge h⟩
  map_add' _ _ := rfl
  map_zero' := rfl

@[simp]
lemma lp.coe_addMonoidHomOfLE_apply (h : p ≤ q) (f : lp E p) :
    ⇑(lp.addMonoidHomOfLE E h f) = f :=
  funext fun _ ↦ rfl

lemma lp.addMonoidHomOfLE_comp (hpq : p ≤ q) (hqr : q ≤ r) :
   (lp.addMonoidHomOfLE E hqr).comp (lp.addMonoidHomOfLE E hpq) =
     lp.addMonoidHomOfLE E (hpq.trans hqr) := by
  ext; rfl

variable (𝕜 E) in
/-- `lp.addMonoidHomOfLE` as a linear map. -/
def lp.linearMapOfLE (h : p ≤ q) :
    lp E p →ₗ[𝕜] lp E q where
  toFun f := ⟨f, lp.memℓp f |>.of_exponent_ge h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma lp.coe_linearMapOfLE_apply (h : p ≤ q) (f : lp E p) :
    ⇑(lp.linearMapOfLE 𝕜 E h f) = f :=
  funext fun _ ↦ rfl

@[simp]
lemma lp.toAddMonoidHom_linearMapOfLE (h : p ≤ q) :
    (lp.linearMapOfLE 𝕜 E h).toAddMonoidHom = lp.addMonoidHomOfLE E h :=
  rfl

lemma lp.linearMapOfLE_comp (hpq : p ≤ q) (hqr : q ≤ r) :
   (lp.linearMapOfLE 𝕜 E hqr).comp (lp.linearMapOfLE 𝕜 E hpq) =
     lp.linearMapOfLE 𝕜 E (hpq.trans hqr) := by
  ext; rfl

variable (E p) in
/-- Evaluation at a single coordinate, as a linear map on `lp E p`. -/
@[simps]
def lp.evalₗ (i : ι) : lp E p →ₗ[𝕜] E i where
  toFun f := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E p) in
/-- Evaluation at a single coordinate, as a continuous linear map on `lp E p`. -/
noncomputable def lp.evalCLM [Fact (1 ≤ p)] (i : ι) : lp E p →L[𝕜] E i :=
  (lp.evalₗ E p i).mkContinuous 1 fun x ↦ by
    have hp : p ≠ 0 := zero_lt_one.trans_le Fact.out |>.ne'
    simpa only [evalₗ_apply, one_mul, ge_iff_le] using lp.norm_apply_le_norm hp x i

/-- The basis for `ℓ⁰(ι, 𝕜)` given by `lp.single`. -/
@[simps]
noncomputable def lp.zeroBasis : Module.Basis ι 𝕜 ℓ^0(ι, 𝕜) where
  repr :=
    { toFun x := .ofSupportFinite ⇑x <| memℓp_zero_iff.mp x.2
      invFun x := ⟨⇑x, memℓp_zero_iff.mpr x.hasFiniteSupport⟩
      map_add' _ _ := Finsupp.ext fun _ ↦ rfl
      map_smul' _ _ := Finsupp.ext fun _ ↦ rfl
      left_inv _ := rfl
      right_inv _ := Finsupp.ext fun _ ↦ rfl }

lemma lp.zeroBasis_apply [DecidableEq ι] (i : ι) :
    lp.zeroBasis i = lp.single 0 i (1 : 𝕜) := by
  ext; simp [zeroBasis, Finsupp.single_apply, Pi.single, Function.update, eq_comm]

end NormedRing

section NontriviallyNormedField

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

end NontriviallyNormedField

end Dependent
