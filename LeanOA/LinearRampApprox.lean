import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open NNReal CStarAlgebra Filter Set Function Metric
open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- i only managed to shave off 5 lines, maybe revert to old proof?
theorem epsilon_compression {ε : ℝ≥0} (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0) (hfc : Continuous f)
    (hf0 : f 0 = 0) (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ x, f x ≤ 1) :
    ‖a - a * cfcₙ f a‖₊ ≤ ε := calc
  _ = ‖cfcₙ (fun x : ℝ ↦ x - x * f x.toNNReal) a‖₊ := by
    rw [cfcₙ_sub _ _, cfcₙ_mul _ _, ← cfcₙ_nnreal_eq_real _ _, cfcₙ_id' _ _]
  _ ≤ _ := nnnorm_cfcₙ_le fun x hx ↦ by
    let y : ℝ≥0 := ⟨x, quasispectrum_nonneg_of_nonneg a ha x hx⟩
    simp only [show x = y by rfl, Real.toNNReal_coe, ← NNReal.coe_mul, ge_iff_le]
    if hy' : y = 0 then simp_all else
    rw [← NNReal.coe_sub (by grw [mul_le_iff_le_one_right (pos_of_ne_zero hy'), hfl]), nnnorm_eq]
    by_cases! h : y ≥ ε
    · simp [hf h]
    · exact le_trans (by simp) h.le

theorem Tendsto_of_epsilon_compression (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0 → ℝ≥0)
    (hfc : ∀ ε > 0, Continuous (f ε)) (hf0 : ∀ ε > 0, f ε 0 = 0)
    (hf : ∀ ε > 0, Set.EqOn (f ε) 1 (Set.Ici ε)) (hfl : ∀ ε > 0, ∀ x, f ε x ≤ 1) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (f ε) a‖₊) (𝓝[>] 0) (𝓝 0) := by
  refine (nhdsGT_basis 0).tendsto_iff (Metric.nhds_basis_closedBall) |>.mpr fun ε hε ↦ ?_
  lift ε to ℝ≥0 using hε.le
  exact ⟨ε, hε, fun δ hδ ↦ by
    simpa using epsilon_compression a ha (f δ) (hfc δ hδ.1)
      (hf0 δ hδ.1) (hf δ hδ.1) (hfl δ  hδ.1) |>.trans hδ.2.le⟩

/-- `ε ↦ x ↦ min 1 (1 / ε * x)` -/
noncomputable def linearRamp (ε x : ℝ≥0) := min 1 (1 / ε * x)

lemma continuous_linearRamp (ε : ℝ≥0) : Continuous (linearRamp ε) :=
  continuous_const.inf (continuous_mul_left (1 / ε))

@[simp] lemma linearRamp_apply (ε : ℝ≥0) : linearRamp ε = min 1 (1 / ε * ·) := rfl

theorem Tendsto_of_linearRamp_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (linearRamp ε) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha linearRamp (fun _ ↦ by simpa using by fun_prop)
    (by simp) (fun _ h _ ↦ by simpa using (one_le_inv_mul₀ h).mpr) (by simp)

theorem Tendsto_of_linearRampSq_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ ((· ^ 2) ∘ (linearRamp ε)) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha (fun ε ↦ (· ^ 2) ∘ (linearRamp ε))
    (fun _ _ ↦ by simpa using by fun_prop) (by simp)
    (fun _ h _ ↦ by simpa using (one_le_inv_mul₀ h).mpr)
    (fun _ _ _ ↦ by simpa using (sq_le_one_iff₀ <| zero_le (min 1 _)).mpr <| min_le_left 1 _)

/-- tent function -/
noncomputable def tent (z δ c x : ℝ≥0) : ℝ≥0 := c * (1 - (x - z) / ‖δ‖₊)

@[simp] lemma tent_apply {z δ c : ℝ≥0} : tent z δ c = fun x ↦ c * (1 - (x - z) / δ) := rfl

lemma tent_le_c (z δ c x) : tent z δ c x ≤ c := by aesop (add simp [mul_le_of_le_one_right])

theorem continuous_tent (z δ c) : Continuous (tent z δ c) :=
  .comp (continuous_const.mul continuous_id) (by fun_prop)

/-- `γ` function from Sakai -/
noncomputable def γ (ε z δ c : ℝ≥0) : ℝ≥0 → ℝ≥0 := fun x ↦ linearRamp ε x + tent z δ c x

-- move to ...?
lemma two_pow_two {R : Type*} [Semiring R] : (2 : R) ^ 2 = 4 := by norm_num

-- move to `Mathlib.Data.Real.Sqrt`
lemma NNReal.one_lt_inv_sqrt {r : ℝ≥0} (hr : 0 < r) (hr1 : r < 1) : 1 < (sqrt r)⁻¹ := by
  rw [lt_inv_iff_mul_lt, ← sq_lt_sq₀] <;> aesop

-- probably inline this unless we need it again? (Jon : I agree. Later, though?)
lemma cutoff {r : ℝ≥0} (hr : 0 < r) (hr1 : r < 1) : min 1 (1 / sqrt r - 1) = 1 ↔ r ≤ 1 / 4 := by
  simp [le_tsub_iff_left (one_lt_inv_sqrt hr hr1).le, le_inv_iff_mul_le (by aesop : sqrt r ≠ 0),
    ← sq_le_sq₀ (by aesop : 0 ≤ 2 * sqrt r), one_add_one_eq_two, mul_pow, two_pow_two, mul_comm]

theorem abstract_approx_add {r x : ℝ≥0} (h0r : 0 < r) (hr1 : r < 1)
    (c f : ℝ≥0 → ℝ≥0) (hcle : ∀ y, c y ≤ min 1 (1 / sqrt r - 1)) (hxr : x < r)
    (hfl : ∀ t, f t ≤ 1) : x * (f x + c x) ^ 2 ≤ 1 := by
  by_cases h : r ≤ 1 / 4
  · rw [(cutoff h0r hr1).mpr h] at hcle
    refine le_trans (mul_le_mul (le_trans hxr.le h) (?_ : _ ≤ (2 : ℝ≥0) ^ 2)
      (by positivity) (by positivity)) (by simp [two_pow_two])
    exact pow_le_pow_left' (one_add_one_eq_two (R := ℝ≥0) ▸ (add_le_add (hfl x) (hcle x))) _
  · rw [← cutoff (by grind) hr1, inf_eq_left, not_le] at h
    simp_rw [min_eq_right_of_lt h] at hcle
    have : x * (f x + c x) ^ 2 ≤ x / r := by
      have : f x + c x ≤ 1 / sqrt r := by
        refine le_trans (add_le_add (hfl x) (hcle x)) (add_tsub_cancel_of_le (α := ℝ≥0) ?_ ▸ le_rfl)
        exact one_div (sqrt r) ▸ one_lt_inv_sqrt (by grind) (by grind) |>.le
      grw [mul_le_mul_of_nonneg_left (pow_le_pow_left' this 2) (by positivity)]
      simp [div_eq_mul_inv]
    grw [this, div_le_one_of_le₀ hxr.le (by positivity)]

theorem abstract_approx_sub {r x : ℝ≥0} (h0r : 0 < r) (hr1 : r < 1)
    (c f : ℝ≥0 → ℝ≥0) (hcle : ∀ y, c y ≤ min 1 (1 / sqrt r - 1)) (hxr : x < r)
    (hfl : ∀ t, f t ≤ 1) : x * (f x - c x) ^ 2 ≤ 1 := by
  refine le_trans ?_ (abstract_approx_add h0r hr1 c f hcle hxr hfl)
  gcongr
  exact le_add_of_le_of_nonneg tsub_le_self (zero_le _)

/- We aim to use abstract_approx_add with δ = (1 - t) / 2, r = (1 + t) / 2 for the t that is
   the center of the tent function. The minimum below selects the c that keeps the height
   of the tent less than min 1 (1 /sqrt r - 1). -/
/-- other tent function -/
noncomputable def t_tent (t : ℝ≥0) := tent t ((1 - t)/2) (min 1 (1 / sqrt ((1 + t) / 2) - 1))

/- Must include a proof that `t_tent` is continuous to ensure cfcₙ works. -/

lemma contr_ave {t : ℝ≥0} (ht1 : t < 1) : (1 + t) / 2 < 1 :=
  div_lt_one_of_lt <| lt_of_lt_of_eq (add_lt_add_right ht1 _) (one_add_one_eq_two)

lemma pos_ave {t : ℝ≥0} (h0t : 0 < t) : 0 < (1 + t)/ 2 := by positivity

lemma t_tent_cap (t : ℝ≥0) (x : ℝ≥0) : t_tent t x ≤ (min 1 (1 / sqrt ((1 + t) / 2) - 1)) := by
  simp only [t_tent, one_div, le_inf_iff]
  exact ⟨mul_le_of_le_one_of_le (min_le_left 1 _) tsub_le_self,
    (le_trans (mul_le_of_le_one_right' tsub_le_self) (min_le_right 1 _))⟩

lemma linearRamp_cap (ε t : ℝ≥0) : linearRamp ε t ≤ 1 := by simp

lemma if_big_t_tent_zero {t x : ℝ≥0} (h : ¬ (x < (1 + t) / 2)) : t_tent t x = 0 := by
  simp only [not_lt, t_tent, sub_def, coe_one, one_div, NNReal.coe_inv, Real.coe_sqrt,
    NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, Nat.ofNat_nonneg, Real.sqrt_div', inv_div,
    tent_apply,
    Real.coe_toNNReal', mul_eq_zero, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add] at h ⊢
  -- maybe attribute stuff for `NNReal` with `grind`
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one] at h
  by_cases ht : (t : ℝ) < 1
  · rw [le_div_iff₀ (by simpa), max_eq_left (by simpa using ht.le)]
    grind
  · left
    rw [min_eq_right]
    · simp only [Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add]
      apply div_le_one_of_le₀ (by grind [Real.sqrt_le_sqrt])
      simp
    simp only [Real.toNNReal_le_one, tsub_le_iff_right]
    apply div_le_of_le_mul₀ (by simp) (by simp)
    rw [Real.sqrt_le_iff]
    simp only [pos_add_self_iff, zero_lt_one, mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg, mul_pow]
    rw [Real.sq_sqrt (by grind)]
    grind

theorem t_tent_linearRamp_approx_add {t ε x : ℝ≥0} (h0t : 0 < t) (ht1 : t < 1)
    (hx : x ≤ 1) : x * (linearRamp ε x + t_tent t x) ^ 2 ≤ 1 := by
  by_cases hxt : x < (1 + t) / 2
  · exact abstract_approx_add (x := x) (pos_ave h0t) (contr_ave ht1) (t_tent t) (linearRamp ε)
      (t_tent_cap t) hxt (linearRamp_cap ε)
  · rw [if_big_t_tent_zero hxt, add_zero, ← one_pow 2]
    have B1 := (sq_le_sq₀ (zero_le (linearRamp ε x)) zero_le_one).mpr (linearRamp_cap ε x)
    simpa using mul_le_mul hx B1

theorem t_tent_linearRamp_approx_sub {t ε x : ℝ≥0} (h0t : 0 < t) (ht1 : t < 1)
    (hx : x ≤ 1) : x * (linearRamp ε x - t_tent t x) ^ 2 ≤ 1 := by
  refine le_trans ?_ (t_tent_linearRamp_approx_add (ε := ε) h0t ht1 hx)
  gcongr
  exact le_add_of_le_of_nonneg tsub_le_self (zero_le _)

theorem continuous_t_tent (t : ℝ≥0) : Continuous (t_tent t) :=
  continuous_tent t ((1 - t)/2) (min 1 (1 / sqrt ((1 + t) / 2) - 1))

theorem continuous_approx_add {ε t : ℝ≥0} :
    Continuous fun (x : ℝ≥0) ↦ x * (linearRamp ε x + t_tent t x) ^ 2 :=
  continuous_id.mul (((continuous_linearRamp ε).add (continuous_t_tent t)).pow 2)

theorem continuous_approx_sub {ε t : ℝ≥0} :
    Continuous fun (x : ℝ≥0) ↦ x * (linearRamp ε x - t_tent t x) ^ 2 :=
  continuous_id.mul (((continuous_linearRamp ε).sub (continuous_t_tent t)).pow 2)

theorem quasispectrum_le_one (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (t : ℝ≥0) :
    t ∈ quasispectrum ℝ≥0 a → t ≤ 1 := by
  have B := (nnnorm_cfcₙ_nnreal_le_iff id a 1).mp
  rw [cfcₙ_id _ _] at B
  exact (B ha1) t

theorem norm_cfcₙ_approx_add {ε t : ℝ≥0} (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (h0t : 0 < t)
    (ht1 : t < 1) : ‖cfcₙ (fun x : ℝ≥0 ↦ x * (linearRamp ε x + t_tent t x) ^ 2) a‖₊ ≤ 1 :=
  nnnorm_cfcₙ_nnreal_le fun x hx ↦
    t_tent_linearRamp_approx_add h0t ht1 (quasispectrum_le_one a ha ha1 x hx)

theorem norm_cfcₙ_approx_sub {ε t : ℝ≥0} (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (h0t : 0 < t)
    (ht1 : t < 1) : ‖cfcₙ (fun x : ℝ≥0 ↦ x * (linearRamp ε x - t_tent t x) ^ 2) a‖₊ ≤ 1 :=
  nnnorm_cfcₙ_nnreal_le fun x hx ↦
    t_tent_linearRamp_approx_sub h0t ht1 (quasispectrum_le_one a ha ha1 x hx)

/- To do:

 * Use cfcₙ and the CStar identity to get from the above that
   `‖a γε‖ ≤ 1` and `‖a sε‖ ≤ 1` with `γε` and `sε`
   the cfcₙ images of the functions `linearRamp ε x + t_tent t x` and
   `linearRamp ε x - t_tent t x`. (These were `γₙ` and `sₙ` in Sakai.)

 -/
