import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

open NNReal CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem epsilon_compression {ε : ℝ≥0} (a : A) (ha : 0 ≤ a) (f : ℝ≥0 → ℝ≥0)
      (hfc : Continuous f) (hf0 : f 0 = 0) (hf : Set.EqOn f 1 (Set.Ici ε)) (hfl : ∀ x ≤ ε, f x ≤ 1)
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
      exact mul_le_of_le_one_right' <| hfl _ (le_of_lt h)
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
     (hfl : ∀ ε > 0, ∀ x ≤ ε, f ε x ≤ 1) :
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
  Tendsto_of_epsilon_compression a ha linearRamp (fun _ ↦ by simpa [linearRamp] using by fun_prop) (by simp)
    (fun _ h _ ↦ by simpa [linearRamp] using (one_le_inv_mul₀ h).mpr) (by simp)

theorem Tendsto_of_linearRampSq_compression (a : A) (ha : 0 ≤ a) :
    Tendsto (fun (ε : ℝ≥0) ↦ ‖a - a * cfcₙ ((· ^ 2) ∘ (linearRamp ε)) a‖₊) (𝓝[>] 0) (𝓝 0) :=
  Tendsto_of_epsilon_compression a ha (fun ε ↦ (· ^ 2) ∘ (linearRamp ε))
    (fun _ _ ↦ by simpa [linearRamp, one_div] using by fun_prop) (by simp)
    (fun _ h _ ↦ by simpa [linearRamp] using (one_le_inv_mul₀ h).mpr)
    (fun _ _ _ _ ↦ by simpa [linearRamp] using
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
