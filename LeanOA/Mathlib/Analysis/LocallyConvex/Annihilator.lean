module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

@[expose] public section

/-! # Annihilators in the strong dual

This file defines the annihilator in `StrongDual R M` of a submodule `W` of a topological module
`M`, and the coannihilator in `M` of a submodule `Φ` of `StrongDual R M`. These are the analogues
for the strong dual of `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator`, and they are
defined in terms of those via the canonical pairing `topDualPairing R M`, so that the two APIs
mirror each other.

## Main definitions

+ `Submodule.strongDualAnnihilator W`: the submodule of `StrongDual R M` consisting of those
  continuous linear functionals which vanish on `W`.
+ `Submodule.strongDualCoannihilator Φ`: the submodule of `M` on which every functional in `Φ`
  vanishes.

## Main statements

+ `Submodule.strongDualAnnihilator_gc`: `strongDualAnnihilator` and `strongDualCoannihilator` form
  an antitone Galois connection.
+ `Submodule.isClosed_strongDualCoannihilator`: the coannihilator is closed.
+ `Submodule.isClosed_toStrongDual_preimage_strongDualAnnihilator`: the annihilator is
  weak⋆ closed.
+ `Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure`: in a locally
  convex space over `ℝ` or `ℂ`, the coannihilator of the annihilator of `W` is the closure of `W`.
+ `Submodule.strongDualCoannihilator_strongDualAnnihilator_eq_topologicalClosure`: over `ℝ` or `ℂ`,
  the annihilator of the coannihilator of `Φ` is the weak⋆ closure of `Φ`.
+ `Submodule.strongDualAnnihilator_eq_polarSubmodule`,
  `Submodule.strongDualCoannihilator_eq_polarSubmodule`: over a nontrivially normed field, these are
  the polars with respect to `topDualPairing`.
-/

open Topology

namespace Submodule

section CommSemiring

variable {R M : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R] [AddCommMonoid M] [TopologicalSpace M] [Module R M]
variable {W : Submodule R M}

/-- The `strongDualAnnihilator` of a submodule `W` is the submodule of continuous linear
functionals `φ` such that `φ w = 0` for all `w ∈ W`. This is the analogue of
`Submodule.dualAnnihilator` for the strong dual. -/
def strongDualAnnihilator (W : Submodule R M) : Submodule R (StrongDual R M) :=
  W.dualAnnihilator.comap (topDualPairing R M)

@[simp]
theorem mem_strongDualAnnihilator (φ : StrongDual R M) :
    φ ∈ W.strongDualAnnihilator ↔ ∀ w ∈ W, φ w = 0 :=
  mem_dualAnnihilator (W := W) _

theorem comap_dualAnnihilator_eq_strongDualAnnihilator (W : Submodule R M) :
    W.dualAnnihilator.comap (topDualPairing R M) = W.strongDualAnnihilator :=
  rfl

theorem map_strongDualAnnihilator_le_dualAnnihilator (W : Submodule R M) :
    W.strongDualAnnihilator.map (topDualPairing R M) ≤ W.dualAnnihilator :=
  map_comap_le _ _

/-- The `strongDualCoannihilator` of a submodule `Φ` of the strong dual is the submodule of `M`
on which every functional in `Φ` vanishes. This is the analogue of `Submodule.dualCoannihilator`
for the strong dual. -/
def strongDualCoannihilator (Φ : Submodule R (StrongDual R M)) : Submodule R M :=
  (Φ.map (topDualPairing R M)).dualCoannihilator

@[simp]
theorem mem_strongDualCoannihilator {Φ : Submodule R (StrongDual R M)} (x : M) :
    x ∈ Φ.strongDualCoannihilator ↔ ∀ φ ∈ Φ, φ x = 0 := by
  simp [strongDualCoannihilator]

theorem dualCoannihilator_map_eq_strongDualCoannihilator (Φ : Submodule R (StrongDual R M)) :
    (Φ.map (topDualPairing R M)).dualCoannihilator = Φ.strongDualCoannihilator :=
  rfl

theorem dualCoannihilator_le_strongDualCoannihilator_comap (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualCoannihilator ≤ (Φ.comap (topDualPairing R M)).strongDualCoannihilator :=
  dualCoannihilator_anti (map_comap_le _ _)

variable (R M) in
theorem strongDualAnnihilator_gc :
    GaloisConnection
      (OrderDual.toDual ∘
        (strongDualAnnihilator : Submodule R M → Submodule R (StrongDual R M)))
      (strongDualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_strongDualAnnihilator, mem_strongDualCoannihilator]
  grind

theorem le_strongDualAnnihilator_iff_le_strongDualCoannihilator
    {U : Submodule R (StrongDual R M)} {V : Submodule R M} :
    U ≤ V.strongDualAnnihilator ↔ V ≤ U.strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).le_iff_le

@[simp]
theorem strongDualAnnihilator_bot : (⊥ : Submodule R M).strongDualAnnihilator = ⊤ :=
  (strongDualAnnihilator_gc R M).l_bot

@[simp]
theorem strongDualAnnihilator_top : (⊤ : Submodule R M).strongDualAnnihilator = ⊥ := by
  rw [eq_bot_iff]
  intro v
  simp_rw [mem_strongDualAnnihilator, mem_bot, mem_top, forall_true_left]
  exact fun h ↦ ContinuousLinearMap.ext h

@[simp]
theorem strongDualCoannihilator_bot :
    (⊥ : Submodule R (StrongDual R M)).strongDualCoannihilator = ⊤ :=
  (strongDualAnnihilator_gc R M).u_top

@[mono]
theorem strongDualAnnihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.strongDualAnnihilator ≤ U.strongDualAnnihilator :=
  (strongDualAnnihilator_gc R M).monotone_l hUV

@[mono]
theorem strongDualCoannihilator_anti {U V : Submodule R (StrongDual R M)} (hUV : U ≤ V) :
    V.strongDualCoannihilator ≤ U.strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).monotone_u hUV

theorem le_strongDualAnnihilator_strongDualCoannihilator (U : Submodule R M) :
    U ≤ U.strongDualAnnihilator.strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).le_u_l U

theorem le_strongDualCoannihilator_strongDualAnnihilator (U : Submodule R (StrongDual R M)) :
    U ≤ U.strongDualCoannihilator.strongDualAnnihilator :=
  (strongDualAnnihilator_gc R M).l_u_le U

theorem strongDualAnnihilator_strongDualCoannihilator_strongDualAnnihilator (U : Submodule R M) :
    U.strongDualAnnihilator.strongDualCoannihilator.strongDualAnnihilator =
      U.strongDualAnnihilator :=
  (strongDualAnnihilator_gc R M).l_u_l_eq_l U

theorem strongDualCoannihilator_strongDualAnnihilator_strongDualCoannihilator
    (U : Submodule R (StrongDual R M)) :
    U.strongDualCoannihilator.strongDualAnnihilator.strongDualCoannihilator =
      U.strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).u_l_u_eq_u U

theorem strongDualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).strongDualAnnihilator = U.strongDualAnnihilator ⊓ V.strongDualAnnihilator :=
  (strongDualAnnihilator_gc R M).l_sup

theorem strongDualCoannihilator_sup_eq (U V : Submodule R (StrongDual R M)) :
    (U ⊔ V).strongDualCoannihilator = U.strongDualCoannihilator ⊓ V.strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).u_inf

theorem strongDualAnnihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).strongDualAnnihilator = ⨅ i : ι, (U i).strongDualAnnihilator :=
  (strongDualAnnihilator_gc R M).l_iSup

theorem strongDualCoannihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R (StrongDual R M)) :
    (⨆ i : ι, U i).strongDualCoannihilator = ⨅ i : ι, (U i).strongDualCoannihilator :=
  (strongDualAnnihilator_gc R M).u_iInf

/-- See also `Submodule.strongDualAnnihilator_inf_eq` for closed subspaces of locally convex
spaces over `ℝ` or `ℂ`. -/
theorem sup_strongDualAnnihilator_le_inf (U V : Submodule R M) :
    U.strongDualAnnihilator ⊔ V.strongDualAnnihilator ≤ (U ⊓ V).strongDualAnnihilator := by
  rw [le_strongDualAnnihilator_iff_le_strongDualCoannihilator, strongDualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_strongDualAnnihilator_strongDualCoannihilator _

theorem iSup_strongDualAnnihilator_le_iInf {ι : Sort*} (U : ι → Submodule R M) :
    ⨆ i : ι, (U i).strongDualAnnihilator ≤ (⨅ i : ι, U i).strongDualAnnihilator := by
  rw [le_strongDualAnnihilator_iff_le_strongDualCoannihilator, strongDualCoannihilator_iSup_eq]
  exact iInf_mono fun i ↦ le_strongDualAnnihilator_strongDualCoannihilator (U i)

@[simp]
lemma coe_strongDualAnnihilator_span (s : Set M) :
    ((span R s).strongDualAnnihilator : Set (StrongDual R M)) =
      {f : StrongDual R M | s ⊆ LinearMap.ker (f : M →ₗ[R] R)} := by
  ext f
  simp only [SetLike.mem_coe, mem_strongDualAnnihilator, Set.mem_ofPred_eq]
  exact span_le (p := LinearMap.ker (f : M →ₗ[R] R))

@[simp]
lemma coe_strongDualCoannihilator_span (s : Set (StrongDual R M)) :
    ((span R s).strongDualCoannihilator : Set M) = {x | ∀ f ∈ s, f x = 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_strongDualCoannihilator, Set.mem_ofPred_eq]
  exact span_le (p := LinearMap.ker ((topDualPairing R M).flip x))

end CommSemiring

section LinearMap

variable {R M₁ M₂ : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R] [AddCommMonoid M₁] [TopologicalSpace M₁] [Module R M₁]
  [AddCommMonoid M₂] [TopologicalSpace M₂] [Module R M₂]

theorem _root_.ContinuousLinearMap.ker_lcomp_eq_strongDualAnnihilator_range
    (f : M₁ →L[R] M₂) :
    LinearMap.ker (f.lcomp R) = (LinearMap.range (f : M₁ →ₗ[R] M₂)).strongDualAnnihilator := by
  ext φ
  simp [ContinuousLinearMap.ext_iff]

theorem _root_.ContinuousLinearMap.range_lcomp_le_strongDualAnnihilator_ker
    (f : M₁ →L[R] M₂) :
    LinearMap.range (f.lcomp R) ≤ (LinearMap.ker (f : M₁ →ₗ[R] M₂)).strongDualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp +contextual

omit [TopologicalSpace M₂] in
theorem _root_.LinearMap.strongDualCoannihilator_range_eq_ker_flip
    (B : M₂ →ₗ[R] StrongDual R M₁) :
    (LinearMap.range B).strongDualCoannihilator =
      LinearMap.ker (topDualPairing R M₁ ∘ₗ B).flip := by
  ext x
  simp [LinearMap.ext_iff (f := (topDualPairing R M₁ ∘ₗ B).flip x)]

end LinearMap

section SeparatingDual

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R] [AddCommGroup M] [TopologicalSpace M] [Module R M]
  [SeparatingDual R M]

@[simp]
theorem strongDualCoannihilator_top :
    (⊤ : Submodule R (StrongDual R M)).strongDualCoannihilator = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_strongDualCoannihilator] at hx
  exact (mem_bot R).mpr <| SeparatingDual.eq_zero_of_forall_dual_eq_zero fun φ ↦ hx φ trivial

@[simp]
theorem strongDualAnnihilator_eq_top_iff {W : Submodule R M} :
    W.strongDualAnnihilator = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ strongDualAnnihilator_bot⟩
  rw [eq_bot_iff, ← strongDualCoannihilator_top (R := R),
    ← le_strongDualAnnihilator_iff_le_strongDualCoannihilator, h]

end SeparatingDual

/-! ### Annihilators as polars

Over a nontrivially normed field, annihilators are the polars of submodules with respect to the
canonical pairings. -/

section Polar

variable {𝕜 M : Type*} [NontriviallyNormedField 𝕜] [AddCommMonoid M] [Module 𝕜 M]

theorem dualAnnihilator_eq_polarSubmodule (W : Submodule 𝕜 M) :
    W.dualAnnihilator = (LinearMap.id : Module.Dual 𝕜 M →ₗ[𝕜] _).flip.polarSubmodule W :=
  SetLike.coe_injective <| by ext; simp [LinearMap.polarSubmodule, LinearMap.polar_subMulAction]

theorem dualCoannihilator_eq_polarSubmodule (Φ : Submodule 𝕜 (Module.Dual 𝕜 M)) :
    Φ.dualCoannihilator = (LinearMap.id : Module.Dual 𝕜 M →ₗ[𝕜] _).polarSubmodule Φ :=
  SetLike.coe_injective <| by ext; simp [LinearMap.polarSubmodule, LinearMap.polar_subMulAction]

variable [TopologicalSpace M]

theorem strongDualAnnihilator_eq_polarSubmodule (W : Submodule 𝕜 M) :
    W.strongDualAnnihilator = (topDualPairing 𝕜 M).flip.polarSubmodule W :=
  SetLike.coe_injective <| by ext; simp [LinearMap.polarSubmodule, LinearMap.polar_subMulAction]

theorem _root_.StrongDual.polarSubmodule_eq_strongDualAnnihilator (W : Submodule 𝕜 M) :
    StrongDual.polarSubmodule 𝕜 W = W.strongDualAnnihilator :=
  (strongDualAnnihilator_eq_polarSubmodule W).symm

theorem strongDualCoannihilator_eq_polarSubmodule (Φ : Submodule 𝕜 (StrongDual 𝕜 M)) :
    Φ.strongDualCoannihilator = (topDualPairing 𝕜 M).polarSubmodule Φ :=
  SetLike.coe_injective <| by ext; simp [LinearMap.polarSubmodule, LinearMap.polar_subMulAction]

end Polar

section Topology

variable {R M : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R] [T1Space R] [AddCommMonoid M] [TopologicalSpace M] [Module R M]

instance isClosed_strongDualCoannihilator (Φ : Submodule R (StrongDual R M)) :
    IsClosed (Φ.strongDualCoannihilator : Set M) := by
  have : (Φ.strongDualCoannihilator : Set M) = ⋂ φ ∈ Φ, (φ : M → R) ⁻¹' {0} := by
    ext; simp
  rw [this]
  exact isClosed_biInter fun φ _ ↦ isClosed_singleton.preimage φ.continuous

/-- The `strongDualAnnihilator` of a submodule is weak⋆ closed. -/
theorem isClosed_toStrongDual_preimage_strongDualAnnihilator (W : Submodule R M) :
    IsClosed (WeakDual.toStrongDual ⁻¹' (W.strongDualAnnihilator : Set (StrongDual R M))) := by
  have : WeakDual.toStrongDual ⁻¹' (W.strongDualAnnihilator : Set (StrongDual R M)) =
      ⋂ w ∈ W, (fun φ : WeakDual R M ↦ φ w) ⁻¹' {0} := by
    ext; simp
  rw [this]
  exact isClosed_biInter fun w _ ↦ isClosed_singleton.preimage (WeakDual.eval_continuous w)

variable [ContinuousAdd M] [ContinuousConstSMul R M]

theorem topologicalClosure_le_strongDualCoannihilator {W : Submodule R M}
    {Φ : Submodule R (StrongDual R M)} (h : W ≤ Φ.strongDualCoannihilator) :
    W.topologicalClosure ≤ Φ.strongDualCoannihilator :=
  W.topologicalClosure_minimal h (isClosed_strongDualCoannihilator Φ)

@[simp]
theorem strongDualAnnihilator_topologicalClosure (W : Submodule R M) :
    W.topologicalClosure.strongDualAnnihilator = W.strongDualAnnihilator :=
  le_antisymm (strongDualAnnihilator_anti W.le_topologicalClosure) <|
    le_strongDualAnnihilator_iff_le_strongDualCoannihilator.mpr <|
      topologicalClosure_le_strongDualCoannihilator <|
        le_strongDualAnnihilator_strongDualCoannihilator W

end Topology

section RCLike

open RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A linear functional whose real part is bounded below on a submodule vanishes on it. -/
private lemma apply_eq_zero_of_forall_lt_re {f : E →ₗ[𝕜] 𝕜} {W : Submodule 𝕜 E} {u : ℝ}
    (h : ∀ w ∈ W, u < re (f w)) {w : E} (hw : w ∈ W) : f w = 0 := by
  by_contra hfw
  have := h _ (W.smul_mem (((u - 1 : ℝ) : 𝕜) * (f w)⁻¹) hw)
  simp [mul_assoc, inv_mul_cancel₀ hfw] at this
  linarith

section LocallyConvex

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- In a locally convex space over `ℝ` or `ℂ`, the `strongDualCoannihilator` of the
`strongDualAnnihilator` of a submodule `W` is the closure of `W`. This is a consequence of the
Hahn–Banach separation theorem. -/
theorem strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure (W : Submodule 𝕜 E) :
    W.strongDualAnnihilator.strongDualCoannihilator = W.topologicalClosure := by
  refine le_antisymm (fun x hx ↦ ?_) <|
    topologicalClosure_le_strongDualCoannihilator <|
      le_strongDualAnnihilator_strongDualCoannihilator W
  by_contra h
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := 𝕜)
    (W.topologicalClosure.restrictScalars ℝ).convex W.isClosed_topologicalClosure h
  have hf₀ : f ∈ W.strongDualAnnihilator := (mem_strongDualAnnihilator f).mpr fun w hw ↦
    apply_eq_zero_of_forall_lt_re (f := f.toLinearMap) hf (W.le_topologicalClosure hw)
  have := hf 0 (zero_mem _)
  simp only [map_zero, (mem_strongDualCoannihilator x).mp hx f hf₀] at hfx this
  linarith

theorem strongDualAnnihilator_strongDualCoannihilator_eq {W : Submodule 𝕜 E}
    (hW : IsClosed (W : Set E)) : W.strongDualAnnihilator.strongDualCoannihilator = W := by
  rw [strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure,
    hW.submodule_topologicalClosure_eq]

theorem forall_mem_strongDualAnnihilator_apply_eq_zero_iff (W : Submodule 𝕜 E) (v : E) :
    (∀ φ ∈ W.strongDualAnnihilator, φ v = 0) ↔ v ∈ W.topologicalClosure := by
  rw [← strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure,
    mem_strongDualCoannihilator]

theorem strongDualAnnihilator_le_strongDualAnnihilator_iff {W W' : Submodule 𝕜 E} :
    W.strongDualAnnihilator ≤ W'.strongDualAnnihilator ↔ W' ≤ W.topologicalClosure := by
  rw [le_strongDualAnnihilator_iff_le_strongDualCoannihilator,
    strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure]

theorem strongDualAnnihilator_inj {W W' : Submodule 𝕜 E} :
    W.strongDualAnnihilator = W'.strongDualAnnihilator ↔
      W.topologicalClosure = W'.topologicalClosure := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← strongDualAnnihilator_strongDualCoannihilator_eq_topologicalClosure, h]
  · rw [← strongDualAnnihilator_topologicalClosure W, h, strongDualAnnihilator_topologicalClosure]

@[simp]
theorem strongDualAnnihilator_eq_bot_iff {W : Submodule 𝕜 E} :
    W.strongDualAnnihilator = ⊥ ↔ Dense (W : Set E) := by
  rw [← strongDualAnnihilator_top, strongDualAnnihilator_inj, dense_iff_topologicalClosure_eq_top,
    top_unique (⊤ : Submodule 𝕜 E).le_topologicalClosure]

/-- The `strongDualAnnihilator` of the intersection of two closed submodules is the weak⋆ closure
(see `Submodule.strongDualCoannihilator_strongDualAnnihilator_eq_topologicalClosure`) of the sum
of their `strongDualAnnihilator`s. See also `Submodule.sup_strongDualAnnihilator_le_inf` for
arbitrary submodules. -/
theorem strongDualAnnihilator_inf_eq {U V : Submodule 𝕜 E} (hU : IsClosed (U : Set E))
    (hV : IsClosed (V : Set E)) :
    (U ⊓ V).strongDualAnnihilator = (U.strongDualAnnihilator ⊔
      V.strongDualAnnihilator).strongDualCoannihilator.strongDualAnnihilator := by
  rw [strongDualCoannihilator_sup_eq, strongDualAnnihilator_strongDualCoannihilator_eq hU,
    strongDualAnnihilator_strongDualCoannihilator_eq hV]

/-- The `strongDualAnnihilator` of an intersection of closed submodules is the weak⋆ closure
(see `Submodule.strongDualCoannihilator_strongDualAnnihilator_eq_topologicalClosure`) of the sum
of their `strongDualAnnihilator`s. See also `Submodule.iSup_strongDualAnnihilator_le_iInf` for
arbitrary submodules. -/
theorem strongDualAnnihilator_iInf_eq {ι : Sort*} {U : ι → Submodule 𝕜 E}
    (hU : ∀ i, IsClosed (U i : Set E)) :
    (⨅ i, U i).strongDualAnnihilator =
      (⨆ i, (U i).strongDualAnnihilator).strongDualCoannihilator.strongDualAnnihilator := by
  simp_rw [strongDualCoannihilator_iSup_eq, strongDualAnnihilator_strongDualCoannihilator_eq (hU _)]

end LocallyConvex

section WeakDual

variable [TopologicalSpace E]

/-- Over `ℝ` or `ℂ`, the `strongDualAnnihilator` of the `strongDualCoannihilator` of a submodule
`Φ` of the strong dual is the weak⋆ closure of `Φ`. This is a consequence of the Hahn–Banach
separation theorem in `WeakDual 𝕜 E`. -/
theorem strongDualCoannihilator_strongDualAnnihilator_eq_topologicalClosure
    (Φ : Submodule 𝕜 (StrongDual 𝕜 E)) :
    Φ.strongDualCoannihilator.strongDualAnnihilator =
      ((Φ.comap (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).toLinearMap).topologicalClosure
        |>.comap (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).toLinearMap) := by
  set Φ' := Φ.comap (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).toLinearMap
  set Ψ := Φ'.topologicalClosure
  have hΨ : Ψ ≤ Φ.strongDualCoannihilator.strongDualAnnihilator.comap
      (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).toLinearMap :=
    topologicalClosure_minimal _ (comap_mono (le_strongDualCoannihilator_strongDualAnnihilator Φ))
      (isClosed_toStrongDual_preimage_strongDualAnnihilator _)
  refine le_antisymm (fun φ hφ ↦ ?_) fun φ hφ ↦ hΨ hφ
  by_contra h
  have : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 E) := inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual 𝕜 E))
  have : LocallyConvexSpace ℝ (WeakDual 𝕜 E) := WeakBilin.locallyConvexSpace
  obtain ⟨f, u, hfφ, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := 𝕜)
    (Ψ.restrictScalars ℝ).convex Φ'.isClosed_topologicalClosure h
  obtain ⟨x, rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 E) f
  have hx : x ∈ Φ.strongDualCoannihilator := (mem_strongDualCoannihilator x).mpr fun ψ hψ ↦
    apply_eq_zero_of_forall_lt_re (f := (WeakBilin.eval (topDualPairing 𝕜 E) x).toLinearMap) hf
      (Φ'.le_topologicalClosure (x := StrongDual.toWeakDual ψ) hψ)
  have := hf 0 (zero_mem _)
  simp only [map_zero] at this
  change re (φ x) < u at hfφ
  rw [(mem_strongDualAnnihilator φ).mp hφ x hx, map_zero] at hfφ
  linarith

/-- If `Φ` is a weak⋆ closed submodule of the strong dual over `ℝ` or `ℂ`, then the
`strongDualAnnihilator` of its `strongDualCoannihilator` is `Φ` itself. -/
theorem strongDualCoannihilator_strongDualAnnihilator_eq {Φ : Submodule 𝕜 (StrongDual 𝕜 E)}
    (hΦ : IsClosed (WeakDual.toStrongDual ⁻¹' (Φ : Set (StrongDual 𝕜 E)))) :
    Φ.strongDualCoannihilator.strongDualAnnihilator = Φ := by
  rw [strongDualCoannihilator_strongDualAnnihilator_eq_topologicalClosure,
    IsClosed.submodule_topologicalClosure_eq (s := Φ.comap _) hΦ]
  ext; simp

theorem forall_mem_strongDualCoannihilator_apply_eq_zero_iff {Φ : Submodule 𝕜 (StrongDual 𝕜 E)}
    (hΦ : IsClosed (WeakDual.toStrongDual ⁻¹' (Φ : Set (StrongDual 𝕜 E))))
    (φ : StrongDual 𝕜 E) : (∀ x ∈ Φ.strongDualCoannihilator, φ x = 0) ↔ φ ∈ Φ := by
  rw [← mem_strongDualAnnihilator, strongDualCoannihilator_strongDualAnnihilator_eq hΦ]

end WeakDual

end RCLike

end Submodule
