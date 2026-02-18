import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open NNReal CStarAlgebra Filter Set Function Metric
open scoped Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem epsilon_compression {ε : ℝ≥0} (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0) (hfc : Continuous f)
    (hf0 : f 0 = 0) (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ x, f x ≤ 1) :
    ‖a - a * cfcₙ f a‖₊ ≤ ε := by
  have H1 (x : ℝ≥0) : x - x * f x ≤ ε := by
    by_cases! h : x ≥ ε
    · simp [hf h]
    · have : x - x * (f x) ≤ x := by
        nth_rw 1 [← mul_one x, ← mul_tsub]
        exact mul_le_of_le_one_right' tsub_le_self
      exact le_trans this h.le
  have H2 (x : ℝ≥0) :  x * f x ≤ x := by
    by_cases! h : x ≥ ε
    · simp [hf h]
    · exact mul_le_of_le_one_right' <| coe_le_one.mp (hfl x)
  nth_rw 1 2 [← cfcₙ_id (R := ℝ≥0) a]
  rw [← cfcₙ_mul id f, ← cfcₙ_tsub id (ha := ha) (fun _ ↦ id _ * f _)]
  · refine nnnorm_cfcₙ_nnreal_le (A := A) fun x _ ↦ H1 (id _)
  · exact fun _ _ ↦ H2 (id _)

theorem Tendsto_of_epsilon_compression (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0 → ℝ≥0)
   (hfc : ∀ ε > 0, Continuous (f ε)) (hf0 : ∀ ε > 0, f ε 0 = 0)
    (hf : ∀ ε > 0, Set.EqOn (f ε) 1 (Set.Ici ε))
    (hfl : ∀ ε > 0, ∀ x, f ε x ≤ 1) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (f ε) a‖₊) (𝓝[>] 0) (𝓝 0) := by
  refine (nhdsGT_basis 0).tendsto_iff (Metric.nhds_basis_closedBall) |>.mpr fun ε hε ↦ ?_
  lift ε to ℝ≥0 using hε.le
  exact ⟨ε, hε, fun δ hδ ↦ by
    simpa using epsilon_compression a ha (f δ) (hfc δ hδ.1)
      (hf0 δ hδ.1) (hf δ hδ.1) (hfl δ  hδ.1) |>.trans hδ.2.le⟩

/-- `ε ↦ x ↦ min 1 (1 / ε * x)` -/
noncomputable def linearRamp (ε x : ℝ≥0) := min 1 (1 / ε * x)

lemma continuous_linearRamp (ε : ℝ≥0) : Continuous (linearRamp ε) :=
  Continuous.inf (continuous_const) (continuous_mul_left (1 / ε))

@[simp]
lemma linearRamp_apply (ε : ℝ≥0) : linearRamp ε = min 1 (1 / ε * ·) := rfl

theorem Tendsto_of_linearRamp_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (linearRamp ε) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha linearRamp (fun _ ↦ by simpa using by fun_prop)
    (by simp) (fun _ h _ ↦ by simpa using (one_le_inv_mul₀ h).mpr) (by simp)

theorem Tendsto_of_linearRampSq_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ ((· ^ 2) ∘ (linearRamp ε)) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha (fun ε ↦ (· ^ 2) ∘ (linearRamp ε))
    (fun _ _ ↦ by simpa using by fun_prop) (by simp)
    (fun _ h _ ↦ by simpa using (one_le_inv_mul₀ h).mpr)
    (fun _ _ _ ↦ by simpa using
      (sq_le_one_iff₀ <| zero_le (min 1 (_⁻¹ * _))).mpr <| min_le_left 1 (_⁻¹ * _))

-- move to `Mathlib.Topology.Order.LeftRightNhds` I think?
lemma nhdsGT_basis_Ioc {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] (a : α) :
    (𝓝[>] a).HasBasis (fun x ↦ a < x) (Ioc a) := nhdsGT_basis a |>.to_hasBasis'
  (fun _ hac ↦
    have ⟨b, hab, hbc⟩ := exists_between hac
    ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
  fun _ hac ↦ mem_of_superset ((nhdsGT_basis a).mem_of_mem hac) Ioo_subset_Ioc_self

/-- tent function -/
noncomputable def tent (z δ c x : ℝ≥0) : ℝ≥0 :=
   c * (1 - (x - z) / ‖δ‖₊)

@[simp]
lemma tent_apply {z δ c : ℝ≥0} : tent z δ c =
  fun x ↦ c * (1 - (x - z) / δ) := rfl

lemma tent_le_c (z δ c x) : tent z δ c x ≤ c := by aesop (add simp [mul_le_of_le_one_right])

theorem continuous_tent (z δ c) : Continuous (tent z δ c) :=
  .comp (continuous_const.mul continuous_id) (by fun_prop)

/-- `γ` function from Sakai -/
noncomputable def γ (ε z δ c : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun x ↦ (linearRamp ε) x + (tent z δ c) x

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

lemma t_tent_cap (t : ℝ≥0) (x : ℝ≥0) :
    t_tent t x ≤ (min 1 (1 / sqrt ((1 + t) / 2) - 1)) := by
  dsimp[t_tent]
  simp only [one_div, le_inf_iff]
  exact ⟨mul_le_of_le_one_of_le (min_le_left 1 ((sqrt ((1 + t) / 2))⁻¹ - 1)) (tsub_le_self),
    (le_trans (mul_le_of_le_one_right' (tsub_le_self))
      (min_le_right 1 ((sqrt ((1 + t) / 2))⁻¹ - 1)))⟩

lemma linearRamp_cap (ε t : ℝ≥0) : linearRamp ε t ≤ 1 := by simp

lemma if_big_t_tent_zero {t x : ℝ≥0} (h : ¬ (x < (1 + t) / 2)) : t_tent t x = 0 := by
  simp only [not_lt, t_tent, sub_def, coe_one, one_div, NNReal.coe_inv, Real.coe_sqrt,
    NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, Nat.ofNat_nonneg, Real.sqrt_div', inv_div,
    tent_apply,
    Real.coe_toNNReal', mul_eq_zero, Real.toNNReal_eq_zero, tsub_le_iff_right, zero_add] at h ⊢
  -- maybe attribute stuff for `NNReal` with `grind`
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one] at h
  by_cases ht : (t : ℝ) < 1
  · right
    rw [le_div_iff₀ (by simpa), max_eq_left (by simpa using ht.le)]
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
      (t_tent_cap t) (hxt) (linearRamp_cap ε)
  · rw [if_big_t_tent_zero hxt, add_zero, ← one_pow 2]
    have B1 := (sq_le_sq₀ ((zero_le (linearRamp ε x))) (zero_le_one)).mpr  <| linearRamp_cap ε x
    have B2 := mul_le_mul hx B1 (by positivity) (by positivity)
    rw [one_mul] at B2
    assumption

theorem t_tent_linearRamp_approx_sub {t ε x : ℝ≥0} (h0t : 0 < t) (ht1 : t < 1)
    (hx : x ≤ 1) : x * (linearRamp ε x - t_tent t x) ^ 2 ≤ 1 := by
  refine le_trans ?_ (t_tent_linearRamp_approx_add (ε := ε) h0t ht1 hx)
  gcongr
  exact le_add_of_le_of_nonneg tsub_le_self (zero_le _)

theorem continuous_t_tent (t : ℝ≥0) : Continuous (t_tent t) :=
  continuous_tent t ((1 - t)/2) (min 1 (1 / sqrt ((1 + t) / 2) - 1))

theorem continuous_approx_add {ε t : ℝ≥0} :
  Continuous fun (x : ℝ≥0) ↦ x * (linearRamp ε x + t_tent t x) ^ 2 :=
  Continuous.mul (continuous_id) (Continuous.pow (Continuous.add
    (continuous_linearRamp ε) (continuous_t_tent t)) 2)

theorem continuous_approx_sub {ε t : ℝ≥0} :
  Continuous fun (x : ℝ≥0) ↦ x * (linearRamp ε x - t_tent t x) ^ 2 :=
  Continuous.mul (continuous_id) (Continuous.pow (Continuous.sub
    (continuous_linearRamp ε) (continuous_t_tent t)) 2)


theorem quasispectrum_le_one (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (t : ℝ≥0) :
    t ∈ quasispectrum ℝ≥0 a → t ≤ 1 := by
 have B := (nnnorm_cfcₙ_nnreal_le_iff id a 1).mp
 have C := cfcₙ_id (R := ℝ≥0) (A := A) (ha := ha)
 simp only [C, id_eq] at B
 have F := B ha1
 intro h
 exact F t h

theorem norm_cfcₙ_approx_add {ε t : ℝ≥0} (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (h0t : 0 < t)
    (ht1 : t < 1) : ‖cfcₙ (fun (x : ℝ≥0) ↦ x * (linearRamp ε x + t_tent t x) ^ 2) a‖₊ ≤ 1 := by
  refine nnnorm_cfcₙ_nnreal_le (A := A) ?_
  intro x hx
  have hx1 : x ≤ 1 := quasispectrum_le_one a ha ha1 x hx
  exact t_tent_linearRamp_approx_add (x := x) (ε := ε) (t := t) h0t ht1 hx1

theorem norm_cfcₙ_approx_sub {ε t : ℝ≥0} (a : A) (ha : 0 ≤ a) (ha1 : ‖a‖₊ ≤ 1) (h0t : 0 < t)
    (ht1 : t < 1) : ‖cfcₙ (fun (x : ℝ≥0) ↦ x * (linearRamp ε x - t_tent t x) ^ 2) a‖₊ ≤ 1 := by
  refine nnnorm_cfcₙ_nnreal_le (A := A) ?_
  intro x hx
  have hx1 : x ≤ 1 := quasispectrum_le_one a ha ha1 x hx
  exact t_tent_linearRamp_approx_sub (x := x) (ε := ε) (t := t) h0t ht1 hx1

/- To do:

 * Use cfcₙ and the CStar identity to get from the above that
   `‖a γε‖ ≤ 1` and `‖a sε‖ ≤ 1` with `γε` and `sε`
   the cfcₙ images of the functions `linearRamp ε x + t_tent t x` and
   `linearRamp ε x - t_tent t x`. (These were `γₙ` and `sₙ` in Sakai.)

 -/
