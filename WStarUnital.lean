import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import LeanOA.Ultraweak.Basic

open CStarAlgebra Topology Filter

open scoped ComplexStarModule Ultraweak

variable {M P : Type*}
variable [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [NormedAddCommGroup P]
variable [NormedSpace ℂ P] [Predual ℂ M P]

protected theorem Ultraweak.continuous_mul_left (m : σ(M, P)) : Continuous (m * ·) := by sorry

protected theorem Ultraweak.continuous_mul_right (m : σ(M, P)) : Continuous (· * m) := by sorry

theorem ClusterPt_of_ApproximateUnit :
  ∃ e ∈ (ofUltraweak (𝕜 := ℂ) (P := P) )⁻¹' (Metric.closedBall (0 : M) 1),
    ClusterPt e (map (toUltraweak (𝕜 := ℂ) (P := P)) (approximateUnit M)) := by
  have := (increasingApproximateUnit M).toIsApproximateUnit |>.3
  exact Set.inter_nonempty.mp (Ultraweak.isCompact_closedBall _ _ _ _ <|
    le_principal_iff.mpr <| mem_inf_of_right fun ⦃a⦄ a_1 ↦ a_1)

theorem LeftUnital {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Predual ℂ M P] :
    ∃ e : σ(M, P), ∀ m, m * e = m := by
  obtain ⟨e, he⟩ : ∃ e, MapClusterPt e (approximateUnit M) (toUltraweak ℂ P) := by
    rcases ClusterPt_of_ApproximateUnit (M := M) (P := P) with ⟨_, hd⟩
    exact ⟨_, hd.2⟩
  use e
  intro m
  obtain ⟨l, hl, hle⟩ := mapClusterPt_iff_ultrafilter.mp he
  have h₁ : Tendsto (m * toUltraweak ℂ P ·) l (𝓝 (m * e)) :=
    -- uses `hle` and one-sided ultraweak continuity of multiplication.
    Tendsto.comp (Continuous.tendsto (Ultraweak.continuous_mul_left _) _) hle
  have h₂ : Tendsto (ofUltraweak m * ·) l (𝓝 (ofUltraweak m)) :=
    -- uses `hl` and the approximate unit property.
    Tendsto.comp ((increasingApproximateUnit M).toIsApproximateUnit.tendsto_mul_left _) hl
  have h₃ : Tendsto (m * toUltraweak ℂ P ·) l (𝓝 m) := by
   -- uses `h₂` and continuity of `toUltraweak`.
   simpa [ofUltraweak_inj] using tendsto_iff_forall_eventually_mem.mpr fun _ a ↦ h₂
     (Continuous.tendsto toUltraweak_continuous (ofUltraweak _) <| a)
  exact tendsto_nhds_unique h₁ h₃

theorem RightUnital {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Predual ℂ M P] :
    ∃ e : σ(M, P), ∀ m, e * m = m := by
  obtain ⟨e, he⟩ : ∃ e, MapClusterPt e (approximateUnit M) (toUltraweak ℂ P) := by
    rcases ClusterPt_of_ApproximateUnit (M := M) (P := P) with ⟨_, hd⟩
    exact ⟨_, hd.2⟩
  use e
  intro m
  obtain ⟨l, hl, hle⟩ := mapClusterPt_iff_ultrafilter.mp he
  have h₁ : Tendsto (toUltraweak ℂ P · * m) l (𝓝 (e * m)) :=
    Tendsto.comp (Continuous.tendsto (Ultraweak.continuous_mul_right _) _) hle
  have h₂ : Tendsto (· * ofUltraweak m) l (𝓝 (ofUltraweak m)) :=
    Tendsto.comp ((increasingApproximateUnit M).toIsApproximateUnit.tendsto_mul_right _) hl
  have h₃ : Tendsto (toUltraweak ℂ P · * m) l (𝓝 m) := by
   simpa [ofUltraweak_inj] using tendsto_iff_forall_eventually_mem.mpr fun _ a ↦ h₂
     (Continuous.tendsto toUltraweak_continuous (ofUltraweak _) <| a)
  exact tendsto_nhds_unique h₁ h₃

#synth Mul σ(M, P)
#synth NonUnitalRing (M, P)
lemma left_unit_eq_right_unit (e : σ(M, P)) : (∀ m, m * e = m) → (∀ m, e * m = m) := by
   intro h m
   have : e * (m * e) = (e * m) * e := by exact NonUnitalRing.mul_assoc (α := σ(M, P))

#exit
instance : CStarAlgebra M where
  one := Classical.choose LeftUnital
