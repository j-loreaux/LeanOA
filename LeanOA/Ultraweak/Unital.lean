import LeanOA.Ultraweak.Basic
import LeanOA.CStarAlgebra.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual

/-! # WStarAlgebras are Unital

This may not deserve its own file, but here it is, provisionally.

-/

open Set Metric WeakBilin ComplexOrder
open scoped Ultraweak

variable {M P : Type*} [NonUnitalCStarAlgebra M] [NormedAddCommGroup P]
  [NormedSpace ℂ P] [Predual ℂ M P]

include P

theorem exists_extremePoint_closedBall_of_ultraweak :
    ∃ x : σ(M, P), x ∈ extremePoints ℝ (ofUltraweak ⁻¹' closedBall 0 1) :=
    IsCompact.extremePoints_nonempty (Ultraweak.isCompact_closedBall ..)
      (nonempty_closedBall.mpr (zero_le_one))

theorem exists_extremePoint_closedBall : ∃ x : M , x ∈ extremePoints ℝ (closedBall 0 1) := by
  obtain ⟨x, hx⟩ := exists_extremePoint_closedBall_of_ultraweak (M := M) (P := P)
  use ofUltraweak x
  exact mem_extremePoints_iff_left.mpr hx

noncomputable abbrev CStarAlgofExtreme : CStarAlgebra M :=
    CStarAlgebra.ofExtremePt <| Classical.choose_spec <| exists_extremePoint_closedBall (P := P)
