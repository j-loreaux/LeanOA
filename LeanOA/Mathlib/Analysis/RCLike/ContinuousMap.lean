import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

variable {A Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace A] [TopologicalSpace Y]

namespace ContinuousMap

variable (𝕜) in
/-- Lifting `C(A, ℝ)` to `C(A, 𝕜)` using `RCLike.ofReal`. -/
@[simps] def realToRCLike (f : C(A, ℝ)) : C(A, 𝕜) where toFun x := RCLike.ofReal (f x)

@[simp] lemma isSelfAdjoint_realToRCLike {f : C(A, ℝ)} : IsSelfAdjoint (f.realToRCLike 𝕜) := by
  ext; simp

@[simp] lemma spectrum_realToRCLike (f : C(A, ℝ)) :
    spectrum ℝ (f.realToRCLike 𝕜) = spectrum ℝ f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

/-- Mapping `C(A, 𝕜)` to `C(A, ℝ)` using `RCLike.re`. -/
@[simps] def rclikeToReal (f : C(A, 𝕜)) : C(A, ℝ) where toFun x := RCLike.re (f x)

@[simp] theorem rclikeToReal_realToRCLike (f : C(A, ℝ)) :
    (f.realToRCLike 𝕜).rclikeToReal = f := by ext; simp

theorem IsSelfAdjoint.realToRCLike_rclikeToReal {f : C(A, 𝕜)} (hf : IsSelfAdjoint f) :
    f.rclikeToReal.realToRCLike 𝕜 = f := by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

variable (𝕜) in
open ContinuousMap in
theorem range_realToRCLike_eq_isSelfAdjoint :
    .range (realToRCLike 𝕜) = {f : C(A, 𝕜) | IsSelfAdjoint f} :=
  le_antisymm (fun _ ⟨_, h⟩ ↦ by simp [← h]) fun f hf ↦
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

variable (𝕜) in
@[simp] theorem isometry_realToRCLike [CompactSpace A] : Isometry (realToRCLike 𝕜 (A := A)) :=
  .of_dist_eq fun f g ↦ by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

end ContinuousMap
