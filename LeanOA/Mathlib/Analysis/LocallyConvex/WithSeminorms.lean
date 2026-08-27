module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section

lemma WithSeminorms.hasBasis_zero_closedBall
    {𝕜 E ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    (nhds 0).HasBasis (fun (sr : Finset ι × ℝ) => 0 < sr.2)
      fun (sr : Finset ι × ℝ) => (sr.1.sup p).closedBall 0 sr.2 := by
  apply hp.hasBasis_ball.to_hasBasis ?_
    fun i hi ↦ ⟨i, hi, Seminorm.ball_subset_closedBall (i.1.sup p) 0 i.2⟩
  refine fun i hi ↦ ⟨(i.1, i.2 / 2), by positivity, ?_⟩
  rw [Seminorm.closedBall_zero_eq_preimage_closedBall, Seminorm.ball_zero_eq_preimage_ball]
  gcongr
  exact Metric.closedBall_subset_ball (half_lt_self hi)

lemma WithSeminorms.hasBasis_zero_closedBall_of_directed
    {𝕜 E ι : Type*} [Nonempty ι] [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (hp_dir : Directed (· ≤ ·) p) :
    (nhds 0).HasBasis (fun (ir : ι × ℝ) => 0 < ir.2)
      fun (ir : ι × ℝ) => (p ir.1).closedBall 0 ir.2 := by
  apply hp.hasBasis_zero_closedBall.to_hasBasis ?_ ?_
  · rintro ⟨s, r⟩ (hr : 0 < r)
    classical
    obtain ⟨-, ⟨i, rfl⟩, hi⟩ := (s.image p).sup_le_of_le_directed _
        (Set.range_nonempty _) hp_dir.directedOn_range <| by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨_, ⟨i, rfl⟩, le_rfl⟩
    have : s.sup p ≤ p i := Finset.sup_le <| by simpa using hi
    exact ⟨(i, r), hr, Seminorm.closedBall_antitone this⟩
  · rintro ⟨i, r⟩ (hr : 0 < r)
    refine ⟨({i}, r), hr, by simp⟩
