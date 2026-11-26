module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section

lemma WithSeminorms.hasBasis_zero_closedBall
    {𝕜 E ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    (nhds 0).HasBasis (fun (sr : Finset ι × ℝ) ↦ 0 < sr.2)
      fun (sr : Finset ι × ℝ) ↦ (sr.1.sup p).closedBall 0 sr.2 :=
  hp.hasBasis_ball.to_hasBasis
    (fun i hi ↦ ⟨(i.1, i.2 / 2), half_pos hi, fun _ (hx : _ ≤ _) ↦ hx.trans_lt (half_lt_self hi)⟩)
    fun i hi ↦ ⟨i, hi, Seminorm.ball_subset_closedBall _ 0 i.2⟩

lemma WithSeminorms.hasBasis_zero_closedBall_of_directed
    {𝕜 E ι : Type*} [Nonempty ι] [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (hp_dir : Directed (· ≤ ·) p) :
    (nhds 0).HasBasis (fun (ir : ι × ℝ) ↦ 0 < ir.2)
      fun (ir : ι × ℝ) ↦ (p ir.1).closedBall 0 ir.2 := by
  apply hp.hasBasis_zero_closedBall.to_hasBasis ?_ ?_
  · rintro ⟨s, r⟩ (hr : 0 < r)
    obtain ⟨i, hi⟩ := hp_dir.finset_le s
    exact ⟨(i, r), hr, Seminorm.closedBall_antitone (Finset.sup_le hi)⟩
  · rintro ⟨i, r⟩ (hr : 0 < r)
    exact ⟨({i}, r), hr, by simp⟩
