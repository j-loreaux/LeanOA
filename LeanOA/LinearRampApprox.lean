import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem epsilon_compression {ε : ℝ≥0} (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0)
      (hfc : Continuous f) (hf0 : f 0 = 0) (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ x, f x ≤ 1)
        : ‖a - a * cfcₙ f a‖₊ ≤ ε := by
  have H1 (x : ℝ≥0) : x - x * f x ≤ ε := by
    by_cases h : x ≥ ε
    · simp [hf h]
    · simp only [ge_iff_le, not_le] at h
      have : x - x * (f x) ≤ x := by
        nth_rw 1 [← mul_one x, ← mul_tsub]
        exact mul_le_of_le_one_right' tsub_le_self
      exact le_trans this (le_of_lt h)
  have H2 (x : ℝ≥0) :  x * f x ≤ x := by
    by_cases h : x ≥ ε
    · rw [hf h, Pi.one_apply, mul_one]
    · simp only [ge_iff_le, not_le] at h
      exact mul_le_of_le_one_right' <| coe_le_one.mp (hfl x)
  nth_rw 1 2 [← cfcₙ_id (R := ℝ≥0) a]
  rw [← cfcₙ_mul id f,
       ← cfcₙ_tsub id (ha := ha) (fun _ ↦ id _ * f _)]
  · refine nnnorm_cfcₙ_nnreal_le (A := A) ?_
    · exact fun x _ ↦ H1 (id _)
  · exact fun _ _ ↦ H2 (id _)

open Filter Set Function

open scoped Topology

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

noncomputable def linearRamp (ε x : ℝ≥0) := min 1 (1 / ε * x)

@[simp]
lemma linearRamp_apply (ε : ℝ≥0) : linearRamp ε = min 1 (1 / ε * ·) := rfl

theorem Tendsto_of_linearRamp_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (linearRamp ε) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha linearRamp (fun _ ↦ by simpa [linearRamp] using by fun_prop)
    (by simp) (fun _ h _ ↦ by simpa [linearRamp] using (one_le_inv_mul₀ h).mpr) (by simp)

theorem Tendsto_of_linearRampSq_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ ((· ^ 2) ∘ (linearRamp ε)) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha (fun ε ↦ (· ^ 2) ∘ (linearRamp ε))
    (fun _ _ ↦ by simpa [linearRamp, one_div] using by fun_prop) (by simp)
    (fun _ h _ ↦ by simpa [linearRamp] using (one_le_inv_mul₀ h).mpr)
    (fun _ _ _ ↦ by simpa [linearRamp] using
      (sq_le_one_iff₀ <| zero_le (min 1 (_⁻¹ * _))).mpr <| min_le_left 1 (_⁻¹ * _))

/- The following should be in Mathlib. -/

lemma nhdsGT_basis_Ioc {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] (a : α) :
    (𝓝[>] a).HasBasis (fun x => a < x) (Ioc a) := by
  apply nhdsGT_basis a |>.to_hasBasis'
  all_goals intro c hac
  · obtain ⟨b, hab, hbc⟩ := exists_between hac
    refine ⟨b, hab, Ioc_subset_Ioo_right hbc⟩
  · exact mem_of_superset ((nhdsGT_basis a).mem_of_mem hac) Ioo_subset_Ioc_self

/- Begin work here on the second paragraph of 1.6.1.-/

/- The following functions might end up the actual witnesses to the argument, but
we need to develop some abstract machinery first. -/

noncomputable def tent (z δ c x : ℝ≥0) : ℝ≥0 :=
   c * (1 - ‖(x.toReal - z.toReal)‖.toNNReal / ‖δ‖₊)

@[simp]
lemma tent_apply {z δ c : ℝ≥0} : tent z δ c =
  fun x ↦ c * (1 - ‖(x.toReal - z.toReal)‖.toNNReal / ‖δ‖₊) := rfl

noncomputable def γ (ε z δ c : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun x ↦ (linearRamp ε) x + (tent z δ c) x

@[simp]
lemma gamma_apply {ε z δ c x : ℝ≥0} : γ ε z δ c x = (linearRamp ε) x + (tent z δ c) x := rfl

noncomputable def s (ε z δ c : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun x ↦ (linearRamp ε) x - (tent z δ c) x

@[simp]
lemma s_apply {ε z δ c x : ℝ≥0} : s ε z δ c x = (linearRamp ε) x - (tent z δ c) x := rfl

/- Missing constraint.-/
lemma s_lt_one (ε z δ c x : ℝ≥0) (hc : c < 1) : γ ε z δ c x < 1 := by
  unfold γ linearRamp tent
  simp only [one_div, nnnorm_eq_self]
  sorry

/- Monica, below are some things you've already seen and cleaned up!-/
lemma two_pow_two {R : Type*} [Semiring R] : (2 : R) ^ 2 = 4 := by norm_num

lemma NNReal.one_lt_inv_sqrt {r : ℝ≥0} (hr : 0 < r) (hr1 : r < 1) : 1 < (sqrt r)⁻¹ := by
  rw [lt_inv_iff_mul_lt, ← sq_lt_sq₀] <;> aesop

lemma cutoff {r : ℝ≥0} (hr : 0 < r) (hr1 : r < 1) : min 1 (1 / sqrt r - 1) = 1 ↔ r ≤ 1 / 4 := by
  simp [le_tsub_iff_left (one_lt_inv_sqrt hr hr1).le, le_inv_iff_mul_le (by aesop : sqrt r ≠ 0),
    ← sq_le_sq₀ (by aesop : 0 ≤ 2 * sqrt r), one_add_one_eq_two, mul_pow, two_pow_two, mul_comm]

example {r : ℝ≥0} (hr : 0 < r) (hr1 : r < 1) : ¬ r ≤ 1 / 4 →
    min 1 (1 / sqrt r - 1) = 1 / sqrt r - 1 := by
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, le_inv_iff_mul_le, not_le,
    inf_eq_right, tsub_le_iff_right]
  intro a
  rw [one_add_one_eq_two]
  sorry

/- I'm wondering which proof is better here, this one or the next? The first has a bunch of
   aesop calls, and the second seems shorter. Neither is really flexible...maybe you have
   a better way! -/
theorem abstract_approx_add {a : A} {s r x ε : ℝ≥0} (ha : a ∈ Metric.ball 0 1)
     (h0s : 0 < s) (hsr : s < r) (hr1 : r < 1) (c f : ℝ≥0 → ℝ≥0)
     (hcle : ∀ y, c y ≤ min 1 (1 / sqrt r - 1)) (hsupp : support c ⊆ Icc s r)
     (hx : x ∈ quasispectrum ℝ≥0 (star a * a)) (hxr : x < r) (hf0 : f 0 = 0)
     (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ t, f t ≤ 1) :
     x * (f x + c x) ^ 2 ≤ 1 := by
  by_cases h : r ≤ 1 / 4
  · exact le_trans (mul_le_mul (le_trans (le_of_lt hxr) h)
      (le_of_le_of_eq ((sq_le_sq₀ (by aesop) (by aesop)).mpr
        (le_of_le_of_eq (add_le_add (hfl _) (le_of_le_of_eq (hcle x)
          ((cutoff (lt_trans h0s hsr) hr1).mpr h))) (one_add_one_eq_two))) (two_pow_two))
            (by aesop) (by aesop)) (by aesop)
  · sorry

theorem abstract_approx_add' {a : A} {s r x ε : ℝ≥0} (ha : a ∈ Metric.ball 0 1)
     (h0s : 0 < s) (hsr : s < r) (hr1 : r < 1) (c f : ℝ≥0 → ℝ≥0)
     (hcle : ∀ y, c y ≤ min 1 (1 / sqrt r - 1)) (hsupp : support c ⊆ Icc s r)
     (hx : x ∈ quasispectrum ℝ≥0 (star a * a)) (hxr : x < r) (hf0 : f 0 = 0)
     (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ t, f t ≤ 1) :
     x * (f x + c x) ^ 2 ≤ 1 := by
  by_cases h : r ≤ 1 / 4
  · rw [(cutoff (lt_trans h0s hsr) hr1).mpr h] at hcle
    exact le_trans (mul_le_mul (le_trans (le_of_lt hxr) h)
      (le_of_le_of_eq (pow_le_pow_left' (le_of_le_of_eq (add_le_add (hfl _) (hcle _))
        (one_add_one_eq_two)) 2) rfl) (sq_nonneg (f x + c x)) (zero_le (1 / 4))) (by norm_num)
  · sorry

/- We also need versions of the above for `x * (f x - c x) ^ 2 ≤ 1`. We actually will put these together
   in the end. -/

theorem partial_isom_of_extreme {a : A} (ha : a ∈ extremePoints (𝕜 := ℝ≥0) (E := A)
    (Metric.ball (0 : A) 1)) : quasispectrum ℝ≥0 (star a * a)  ⊆ {0, 1} := by
  by_contra h
  obtain ⟨t, ht1, ht2⟩ := Set.not_subset.mp h
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht2
  push_neg at ht2
  have zero_lt := lt_of_le_of_ne (zero_le t) ht2.1.symm
  have lt_one : t < 1 := by
    have le_one : t ≤ 1 := sorry
    exact lt_of_le_of_ne le_one ht2.2
  let δ := min t / 2 <| (1 - t) /2
  sorry
