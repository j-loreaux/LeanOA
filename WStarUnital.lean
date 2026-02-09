import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import LeanOA.Ultraweak.Basic

open CStarAlgebra Topology Filter

open scoped ComplexStarModule Ultraweak

variable {M P : Type*}
variable [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [NormedAddCommGroup P]
variable [NormedSpace ℂ P] [Predual ℂ M P]

theorem CtsAtLeftMul (m a : M) :
  ContinuousAt (fun (x : σ(M, P)) ↦ (toUltraweak (𝕜 := ℂ) (P := P)) (m * (ofUltraweak x))) a := by
  sorry

theorem ClusterPt_of_ApproxUnit :
  ∃ e ∈ (ofUltraweak (𝕜 := ℂ) (P := P) )⁻¹' (Metric.closedBall (0 : M) 1),
    ClusterPt e (map (toUltraweak (𝕜 := ℂ) (P := P)) (approximateUnit M)) := by
  have : NeBot <| approximateUnit M :=
    IsApproximateUnit.iff_neBot_and_le_nhds_one (l := approximateUnit _) |>.mp
    (increasingApproximateUnit M).toIsApproximateUnit |>.1
  refine Set.inter_nonempty.mp (Ultraweak.isCompact_closedBall _ _ _ _ <|
    le_principal_iff.mpr <| mem_inf_of_right fun ⦃a⦄ a_1 ↦ a_1)

theorem LeftUnital {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Predual ℂ M P] (e : σ(M, P))
    (h : e ∈ (ofUltraweak (𝕜 := ℂ) (P := P)) ⁻¹' (Metric.closedBall (0 : M) 1) ∧
    ClusterPt e (map (toUltraweak (𝕜 := ℂ) (P := P)) (approximateUnit M))) :
    ∀ m : M, (toUltraweak ℂ P m) * e = toUltraweak ℂ P m := by
  intro m
  have A := ContinuousAt.mapClusterPt (CtsAtLeftMul (P := P) m e) h.2
  dsimp [MapClusterPt, ClusterPt] at A
  have U : Tendsto (m * ·) (approximateUnit M) (𝓝 (toUltraweak ℂ P m)) :=
     (increasingApproximateUnit M).toIsApproximateUnit.tendsto_mul_left m
  by_cases hh : (toUltraweak ℂ P m) * e = toUltraweak ℂ P m
  · assumption
  · exfalso
    push_neg at hh
    have WW: 𝓝 (toUltraweak ℂ P m * e) ⊓ map (fun x ↦ toUltraweak ℂ P m * x) (map (toUltraweak ℂ P)
      (approximateUnit M)) ≤ 𝓝 (toUltraweak ℂ P m * e) := inf_le_left
    have Gog := ((disjoint_nhds_nhds (X := σ(M, P))).mpr hh) WW
    rw [neBot_iff] at A
    rw [le_bot_iff] at Gog
    rw [Gog] at A
    · contradiction
    · dsimp [Tendsto] at U
      have arg : 𝓝 (toUltraweak ℂ P m * e) ⊓
        map (fun x ↦ toUltraweak ℂ P m * x) (map (toUltraweak ℂ P) (approximateUnit M)) ≤
          𝓝 (toUltraweak ℂ P m * e) ⊓ 𝓝 (toUltraweak ℂ P m) := by
        refine inf_le_inf_left (α := Filter σ(M, P)) ?_ ?_
        convert U
        refine Eq.symm (TopologicalSpace.ext ?_)
        sorry
      have arghh: 𝓝 (toUltraweak ℂ P m * e) ⊓ 𝓝 (toUltraweak ℂ P m) ≤
        𝓝 (toUltraweak ℂ P m) := inf_le_right
      have := le_trans arg arghh
      exact le_def.mpr this
