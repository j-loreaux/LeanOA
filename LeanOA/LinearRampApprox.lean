import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma abstract_squash1 {ε : ℝ≥0} (x : ℝ≥0) (f : ℝ≥0 → ℝ≥0)
    (hf : Set.EqOn f 1 (Set.Ici ε)) : x - x * f x ≤ ε := by
  by_cases h : x ≥ ε
  · simp [hf h]
  · simp only [ge_iff_le, not_le] at h
    have : x - x * (f x) ≤ x := by
       nth_rw 1 [← mul_one x, ← mul_tsub]
       exact mul_le_of_le_one_right' tsub_le_self
    exact le_trans this (le_of_lt h)

lemma abstract_squash2 {ε : ℝ≥0} (x : ℝ≥0) (f : ℝ≥0 → ℝ≥0)
    (hf1 : Set.EqOn f 1 (Set.Ici ε)) (hf2 : ∀ x ≤ ε, f x ≤ 1) : x * f x ≤ x := by
  by_cases h : x ≥ ε
  · rw [hf1 h, Pi.one_apply, mul_one]
  · simp only [ge_iff_le, not_le] at h
    exact mul_le_of_le_one_right' <| hf2 x (le_of_lt h)

theorem abstract_alg_squash {ε : ℝ≥0} (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0)
      (hfc : Continuous f) (hf0 : f 0 = 0) (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ x ≤ ε, f x ≤ 1)
        : ‖a - a * cfcₙ f a‖₊ ≤ ε := by
  nth_rw 1 2 [← cfcₙ_id (R := ℝ≥0) a]
  rw [← cfcₙ_mul (R := ℝ≥0) id f,
       ← cfcₙ_tsub id (ha := ha) (fun x ↦ id x * f x)]
  · refine nnnorm_cfcₙ_nnreal_le (A := A) ?_
    · exact fun x a ↦ abstract_squash1 (id x) f hf
  · intro x hx
    exact abstract_squash2 (id x) f hf hfl

open Filter Set Function

open scoped Topology

theorem abstract_convergence (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0 → ℝ≥0)
   (hfc : ∀ ε > 0, Continuous (f ε)) (hf0 : ∀ ε > 0, f ε 0 = 0)
     (hf : ∀ ε > 0, Set.EqOn (f ε) 1 (Set.Ici ε))
     (hfl : ∀ ε > 0, ∀ x ≤ ε, f ε x ≤ 1) :
       Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (f ε) a‖₊) (𝓝[>] 0) (𝓝 0) := by
  refine (nhdsGT_basis 0).tendsto_iff (Metric.nhds_basis_closedBall) |>.mpr fun ε hε ↦ ?_
  lift ε to ℝ≥0 using hε.le
  exact ⟨⟨ε, hε.le⟩, hε, fun δ hδ ↦ by
    simpa using abstract_alg_squash a ha (f δ) (hfc δ hδ.1)
      (hf0 δ hδ.1) (hf δ hδ.1) (hfl δ  hδ.1) |>.trans hδ.2.le⟩

noncomputable def linearRamp (ε x : ℝ≥0) := min 1 (1 / ε * x)

@[simp]
lemma linearRamp_apply (ε : ℝ≥0) : linearRamp ε = min 1 (1 / ε * ·) := rfl

theorem linearRamp_converge (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ (linearRamp ε) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  abstract_convergence a ha linearRamp
      (by intro ε
          rw [linearRamp_apply]
          fun_prop)
       (by simp)
       (by dsimp only [Set.Ici, Set.EqOn, Set.mem_setOf_eq, Pi.one_apply]
           simp only [linearRamp, one_div, inf_eq_left]
           intro ε
           exact fun h _ ↦ (one_le_inv_mul₀ h).mpr)
       (by simp)

theorem linearRampSq_converge (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ ((· ^ 2) ∘ (linearRamp ε)) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  abstract_convergence a ha (fun ε ↦ (· ^ 2) ∘ (linearRamp ε))
    (by intro ε hε
        simp only [linearRamp_apply, one_div]
        fun_prop)
    (by simp)
    (by dsimp only [Set.Ici, Set.EqOn, Set.mem_setOf_eq, Pi.one_apply, linearRamp]
        simp only [linearRamp_apply, one_div, Function.comp_apply, Pi.inf_apply, Pi.one_apply,
          pow_eq_one_iff, inf_eq_left, OfNat.ofNat_ne_zero, or_false]
        intro ε
        exact fun h _ ↦ (one_le_inv_mul₀ h).mpr)
    (by intro x hx ε hε
        simp only [linearRamp_apply, one_div, Function.comp_apply, Pi.inf_apply, Pi.one_apply]
        exact (sq_le_one_iff₀ <| zero_le (min 1 (x⁻¹ * ε))).mpr <| min_le_left 1 (x⁻¹ * ε))
