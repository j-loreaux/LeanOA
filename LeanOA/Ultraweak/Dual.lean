module

public import LeanOA.Ultraweak.Basic
public import LeanOA.IsWeak
public import LeanOA.KreinSmulian
public import Mathlib.Analysis.Normed.Module.DoubleDual

@[expose] public section

/-! # The ultraweakly continuous linear functionals

This file identifies the ultraweakly continuous linear functionals on `σ(M, P)_𝕜` with the
predual `P`, and collects the consequences of the Krein–Smulian theorem that are used to test
ultraweak continuity of linear maps on the closed unit ball.

## Main declarations

+ `Predual.toDual`: the canonical isometric embedding of the predual `P` into the dual of `M`.
+ `Ultraweak.continuous_iff_exists_eq`: a linear functional on `M` is ultraweakly continuous if
  and only if it is evaluation at some element of `P`.
+ `Ultraweak.isClosed_setOf_continuous`: the ultraweakly continuous functionals form a norm
  closed subspace of the dual of `M`.
+ `Ultraweak.continuous_of_continuousOn_closedBall`: a linear map out of `σ(M, P)_𝕜` into a
  space with a weak topology is continuous if it is continuous on the closed unit ball.
+ `Ultraweak.continuous_of_isIdempotentElem`: a bounded idempotent linear map on `σ(M, P)_𝕜`
  with closed range and closed kernel is continuous.
-/

open scoped Ultraweak NNReal Topology
open Metric Filter

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

namespace Predual

variable (𝕜 M P) in
/-- The canonical isometric embedding of the predual `P` into the dual of `M`, sending
`p : P` to the functional `m ↦ equivDual m p`. -/
noncomputable def toDual : P →ₗᵢ[𝕜] StrongDual 𝕜 M where
  toFun p := (NormedSpace.inclusionInDoubleDual 𝕜 P p).comp
    (equivDual (𝕜 := 𝕜) (M := M) (P := P)).toContinuousLinearEquiv.toContinuousLinearMap
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  norm_map' p := by
    rw [LinearMap.coe_mk, AddHom.coe_mk]
    exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _).trans <|
      (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map p

@[simp]
lemma toDual_apply (p : P) (m : M) : toDual 𝕜 M P p m = equivDual (𝕜 := 𝕜) m p := rfl

lemma isClosed_range_toDual [CompleteSpace P] :
    IsClosed (Set.range (toDual 𝕜 M P)) :=
  (toDual 𝕜 M P).isometry.isClosedEmbedding.isClosed_range

end Predual

namespace Ultraweak

variable (𝕜 M P) in
/-- The pairing between `σ(M, P)_𝕜` and `P` which induces the ultraweak topology. -/
noncomputable abbrev pairing : σ(M, P)_𝕜 →ₗ[𝕜] P →ₗ[𝕜] 𝕜 :=
  WeakBilin.pairing (topDualPairing 𝕜 P ∘ₗ (Predual.equivDual (M := M)).toLinearEquiv.toLinearMap)

@[simp]
lemma pairing_apply (x : σ(M, P)_𝕜) (p : P) :
    pairing 𝕜 M P x p = Predual.equivDual (𝕜 := 𝕜) (ofUltraweak x) p :=
  rfl

/-- A linear functional on `M` is ultraweakly continuous if and only if it is evaluation at some
element of the predual. -/
theorem continuous_iff_exists_eq (f : M →ₗ[𝕜] 𝕜) :
    Continuous (fun x : σ(M, P)_𝕜 ↦ f (ofUltraweak x)) ↔
      ∃ p : P, ∀ m, f m = Predual.equivDual (𝕜 := 𝕜) m p := by
  refine ⟨fun hf ↦ ?_, fun ⟨p, hp⟩ ↦ by simpa [hp] using eval_continuous (𝕜 := 𝕜) (M := M) p⟩
  obtain ⟨p, hp⟩ := LinearMap.IsWeak.eval_surjective (pairing 𝕜 M P)
    ⟨f ∘ₗ (linearEquiv 𝕜 M P).toLinearMap, hf⟩
  exact ⟨p, fun m ↦ congr($hp (toUltraweak 𝕜 P m)).symm⟩

/-- A norm continuous linear functional on `M` is ultraweakly continuous if and only if it lies in
the range of the canonical embedding of the predual. -/
theorem continuous_iff_mem_range (f : StrongDual 𝕜 M) :
    Continuous (fun x : σ(M, P)_𝕜 ↦ f (ofUltraweak x)) ↔ f ∈ Set.range (Predual.toDual 𝕜 M P) := by
  refine (continuous_iff_exists_eq (P := P) (f : M →ₗ[𝕜] 𝕜)).trans ?_
  exact ⟨fun ⟨p, hp⟩ ↦ ⟨p, by ext m; exact (hp m).symm⟩, fun ⟨p, hp⟩ ↦ ⟨p, fun m ↦ by simp [← hp]⟩⟩

/-- The ultraweakly continuous linear functionals form a norm closed subset of the dual. -/
theorem isClosed_setOf_continuous [CompleteSpace P] :
    IsClosed {f : StrongDual 𝕜 M | Continuous (fun x : σ(M, P)_𝕜 ↦ f (ofUltraweak x))} := by
  rw [show {f : StrongDual 𝕜 M | _} = _ from Set.ext continuous_iff_mem_range]
  exact Predual.isClosed_range_toDual

variable [CompleteSpace P]

set_option backward.isDefEq.respectTransparency false in
/-- **Krein–Smulian** for linear functionals: a linear functional on `σ(M, P)_𝕜` is continuous
if it is continuous on the closed unit ball. -/
theorem continuous_of_continuousOn_closedBall_of_dual (f : σ(M, P)_𝕜 →ₗ[𝕜] 𝕜)
    (hf : ContinuousOn f (ofUltraweak ⁻¹' closedBall (0 : M) 1)) :
    Continuous f := by
  -- transport the problem to the weak dual of `P`, then apply Krein–Smulian there.
  let e := weakDualCLE 𝕜 M P
  let g : WeakDual 𝕜 P →ₗ[𝕜] 𝕜 := f ∘ₗ e.symm.toLinearEquiv.toLinearMap
  suffices Continuous g by
    simpa [g, Function.comp_def] using this.comp (map_continuous e)
  refine g.continuous_of_isClosed_ker <| krein_smulian_of_submodule (g.ker.restrictScalars ℝ≥0) ?_
  have hg : ContinuousOn g (WeakDual.toStrongDual ⁻¹' closedBall 0 1) := by
    refine hf.comp (map_continuous e.symm).continuousOn fun x hx ↦ ?_
    rw [ofUltraweak_preimage_closedBall]
    simpa [e] using hx
  rw [Set.inter_comm]
  exact hg.preimage_isClosed_of_isClosed (WeakDual.isClosed_closedBall 0 1) isClosed_singleton

/-- A linear map from `σ(M, P)_𝕜` into a space carrying the weak topology of a pairing is
continuous if it is continuous on the closed unit ball. -/
theorem continuous_of_continuousOn_closedBall {X F : Type*} [AddCommGroup X] [Module 𝕜 X]
    [TopologicalSpace X] [AddCommGroup F] [Module 𝕜 F] (B : X →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [B.IsWeak]
    (f : σ(M, P)_𝕜 →ₗ[𝕜] X) (hf : ContinuousOn f (ofUltraweak ⁻¹' closedBall (0 : M) 1)) :
    Continuous f :=
  LinearMap.IsWeak.continuous_of_continuous_eval B fun y ↦
    continuous_of_continuousOn_closedBall_of_dual (B.flip y ∘ₗ f) <|
      (LinearMap.IsWeak.continuous_eval B y).comp_continuousOn hf

/-- A bounded idempotent linear map on `σ(M, P)_𝕜` whose range and kernel are both ultraweakly
closed is ultraweakly continuous. -/
theorem continuous_of_isIdempotentElem (E : σ(M, P)_𝕜 →ₗ[𝕜] σ(M, P)_𝕜) (hE : IsIdempotentElem E)
    (C : ℝ) (hC : ∀ x, ‖ofUltraweak (E x)‖ ≤ C * ‖ofUltraweak x‖)
    (h_range : IsClosed (Set.range E)) (h_ker : IsClosed (LinearMap.ker E : Set (σ(M, P)_𝕜))) :
    Continuous E := by
  refine continuous_of_continuousOn_closedBall (pairing 𝕜 M P) E fun x hx ↦ ?_
  have hE' (y : σ(M, P)_𝕜) : E (E y) = E y := congr($hE y)
  /- `E` maps the closed unit ball into the compact set `ofUltraweak ⁻¹' closedBall 0 C`, so it
  suffices to show that every cluster point `y` of `E` at `x` within the ball is `E x`. -/
  refine isCompact_closedBall 𝕜 P (0 : M) (max C 0) |>.tendsto_nhds_of_unique_mapClusterPt ?_
    fun y _ hy ↦ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_preimage, mem_closedBall, dist_zero_right] at hz ⊢
    calc ‖ofUltraweak (E z)‖ ≤ C * ‖ofUltraweak z‖ := hC z
      _ ≤ max C 0 * ‖ofUltraweak z‖ := by gcongr; exact le_max_left C 0
      _ ≤ max C 0 := mul_le_of_le_one_right (le_max_right C 0) hz
  /- Along an ultrafilter `l` at which `E` tends to `y`, the map `id - E` tends to `x - y`.
  Since `id - E` takes values in `ker E` and `E` in `range E`, both of which are closed, we
  obtain `E (x - y) = 0` and `E y = y`, so that `y = E x`. -/
  obtain ⟨l, hl, hly⟩ := mapClusterPt_iff_ultrafilter.mp hy
  have hl' : Tendsto id (l : Filter (σ(M, P)_𝕜)) (𝓝 x) := hl.trans nhdsWithin_le_nhds
  have h₁ : x - y ∈ LinearMap.ker E :=
    h_ker.mem_of_tendsto (hl'.sub hly) <| .of_forall fun z ↦ by simp [hE']
  have h₂ : y ∈ Set.range E := h_range.mem_of_tendsto hly <| .of_forall fun z ↦ ⟨z, rfl⟩
  obtain ⟨w, rfl⟩ := h₂
  exact (sub_eq_zero.mp (by simpa [hE'] using h₁)).symm

end Ultraweak
