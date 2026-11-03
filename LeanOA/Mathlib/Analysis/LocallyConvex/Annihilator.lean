/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.LinearAlgebra.Dual.Defs
public import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar

/-! # Annihilators as polars of submodules

Given a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` over a nontrivially normed field, the polar of a
submodule `W` of `E` is the submodule `B.polarSubmodule W` of `F` consisting of those `y` for which
`B x y = 0` for all `x ∈ W`. This file develops the API of `LinearMap.polarSubmodule`, which plays
the role of the *annihilator* of `W`, while `B.flip.polarSubmodule Φ` plays the role of the
*coannihilator* of a submodule `Φ` of `F`.

Since both are instances of the same construction (applied to `B` and `B.flip`, respectively), most
results need only be stated once. For example, `LinearMap.polarSubmodule_sup` gives both the
annihilator and the coannihilator of a supremum.

The usual annihilators in the (weak or strong) dual are recovered by specializing `B`:
* `(topDualPairing 𝕜 E).flip : E →ₗ[𝕜] StrongDual 𝕜 E →ₗ[𝕜] 𝕜` for the annihilator in the strong
  dual of a submodule of `E`; this satisfies `LinearMap.IsCompatibleDual` (see
  `topDualPairing_flip_isCompatibleDual`).
* `weakDualPairing 𝕜 E : WeakDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜` for the coannihilator of a submodule of the
  weak dual; this satisfies `LinearMap.IsWeak`.

## Main statements

* `LinearMap.polarSubmodule_gc`: `B.polarSubmodule` and `B.flip.polarSubmodule` form an antitone
  Galois connection.
* `LinearMap.isClosed_polarSubmodule_of_continuous`: the polar of a submodule is closed when each
  `B x` is continuous.
* `LinearMap.IsWeak.flip_polarSubmodule_polarSubmodule`: if `E` carries the weak topology induced
  by `B`, then the bipolar of a submodule `W` of `E` is its closure.
* `LinearMap.IsCompatibleDual.flip_polarSubmodule_polarSubmodule`: if `E` is a locally convex space
  whose topology is compatible with `B`, then the bipolar of a submodule `W` of `E` is its closure.
-/

@[expose] public section

open Submodule

variable {𝕜 E F : Type*}

namespace Submodule

open scoped ComplexOrder

/-- Submodules are absolutely convex. -/
protected theorem absConvex [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E] (W : Submodule 𝕜 E) :
    AbsConvex 𝕜 (W : Set E) :=
  ⟨fun a _ ↦ Set.smul_set_subset_iff.mpr fun _ hx ↦ W.smul_mem a hx, W.convex⟩

theorem closedAbsConvexHull_eq_topologicalClosure [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] (W : Submodule 𝕜 E) :
    closedAbsConvexHull 𝕜 (W : Set E) = W.topologicalClosure :=
  subset_antisymm
    (closedAbsConvexHull_min (W.topologicalClosure_coe ▸ subset_closure)
      W.topologicalClosure.absConvex W.isClosed_topologicalClosure)
    (W.topologicalClosure_coe ▸ closure_subset_closedAbsConvexHull)

end Submodule

/-- The canonical pairing of `E` with its strong dual is compatible with the topology on `E`. -/
instance topDualPairing_flip_isCompatibleDual [NontriviallyNormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] : (topDualPairing 𝕜 E).flip.IsCompatibleDual :=
  (LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)).IsCompatibleDual _ rfl

namespace LinearMap

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

section SetLike

variable {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E]

theorem coe_polarSubmodule (m : S) : (B.polarSubmodule m : Set F) = B.polar m :=
  rfl

@[simp]
theorem mem_polarSubmodule {m : S} {y : F} : y ∈ B.polarSubmodule m ↔ ∀ x ∈ m, B x y = 0 := by
  rw [← SetLike.mem_coe, coe_polarSubmodule, polar_subMulAction, Set.mem_ofPred_eq]

theorem polarSubmodule_eq_biInf (m : S) : B.polarSubmodule m = ⨅ x ∈ m, ker (B x) := by
  ext; simp

end SetLike

variable {B}

theorem polarSubmodule_eq_comap_dualAnnihilator (W : Submodule 𝕜 E) :
    B.polarSubmodule W = comap B.flip W.dualAnnihilator := by
  ext; simp

theorem flip_polarSubmodule_eq_dualCoannihilator_map (Φ : Submodule 𝕜 F) :
    B.flip.polarSubmodule Φ = (map B.flip Φ).dualCoannihilator := by
  ext; simp

theorem map_polarSubmodule_le_dualAnnihilator (W : Submodule 𝕜 E) :
    map B.flip (B.polarSubmodule W) ≤ W.dualAnnihilator := by
  rw [polarSubmodule_eq_comap_dualAnnihilator]
  exact map_comap_le _ _

theorem dualCoannihilator_le_flip_polarSubmodule_comap (Φ : Submodule 𝕜 (Module.Dual 𝕜 E)) :
    Φ.dualCoannihilator ≤ B.flip.polarSubmodule (comap B.flip Φ) := by
  rw [flip_polarSubmodule_eq_dualCoannihilator_map]
  exact dualCoannihilator_anti (map_comap_le _ _)

variable (B) in
/-- `B.polarSubmodule` and `B.flip.polarSubmodule` form an antitone Galois connection between the
submodules of `E` and the submodules of `F`. -/
theorem polarSubmodule_gc :
    GaloisConnection (OrderDual.toDual ∘ B.polarSubmodule (S := Submodule 𝕜 E))
      (B.flip.polarSubmodule (S := Submodule 𝕜 F) ∘ OrderDual.ofDual) := fun W Φ ↦ by
  induction Φ using OrderDual.rec
  grind [OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_polarSubmodule, flip_apply]

theorem le_polarSubmodule_iff {Φ : Submodule 𝕜 F} {W : Submodule 𝕜 E} :
    Φ ≤ B.polarSubmodule W ↔ W ≤ B.flip.polarSubmodule Φ :=
  (polarSubmodule_gc B).le_iff_le

@[simp]
theorem polarSubmodule_bot : B.polarSubmodule (⊥ : Submodule 𝕜 E) = ⊤ :=
  (polarSubmodule_gc B).l_bot

theorem polarSubmodule_top : B.polarSubmodule (⊤ : Submodule 𝕜 E) = ker B.flip := by
  ext; simp [LinearMap.ext_iff]

@[simp]
theorem polarSubmodule_top_eq_bot_iff :
    B.polarSubmodule (⊤ : Submodule 𝕜 E) = ⊥ ↔ B.SeparatingRight := by
  rw [polarSubmodule_top, separatingRight_iff_flip_ker_eq_bot]

alias ⟨_, SeparatingRight.polarSubmodule_top⟩ := polarSubmodule_top_eq_bot_iff

theorem polarSubmodule_eq_top_iff (hB : B.SeparatingLeft) {W : Submodule 𝕜 E} :
    B.polarSubmodule W = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, by simp +contextual⟩
  rw [eq_bot_iff, ← (flip_separatingRight.mpr hB).polarSubmodule_top, ← le_polarSubmodule_iff, h]

@[mono]
theorem polarSubmodule_anti {U V : Submodule 𝕜 E} (hUV : U ≤ V) :
    B.polarSubmodule V ≤ B.polarSubmodule U :=
  (polarSubmodule_gc B).monotone_l hUV

theorem le_flip_polarSubmodule_polarSubmodule (W : Submodule 𝕜 E) :
    W ≤ B.flip.polarSubmodule (B.polarSubmodule W) :=
  (polarSubmodule_gc B).le_u_l W

theorem le_polarSubmodule_flip_polarSubmodule (Φ : Submodule 𝕜 F) :
    Φ ≤ B.polarSubmodule (B.flip.polarSubmodule Φ) :=
  (polarSubmodule_gc B).l_u_le Φ

@[simp]
theorem polarSubmodule_flip_polarSubmodule_polarSubmodule (W : Submodule 𝕜 E) :
    B.polarSubmodule (B.flip.polarSubmodule (B.polarSubmodule W)) = B.polarSubmodule W :=
  (polarSubmodule_gc B).l_u_l_eq_l W

@[simp]
theorem flip_polarSubmodule_polarSubmodule_flip_polarSubmodule (Φ : Submodule 𝕜 F) :
    B.flip.polarSubmodule (B.polarSubmodule (B.flip.polarSubmodule Φ)) = B.flip.polarSubmodule Φ :=
  (polarSubmodule_gc B).u_l_u_eq_u Φ

theorem polarSubmodule_sup (U V : Submodule 𝕜 E) :
    B.polarSubmodule (U ⊔ V) = B.polarSubmodule U ⊓ B.polarSubmodule V :=
  (polarSubmodule_gc B).l_sup

theorem polarSubmodule_iSup {ι : Sort*} (U : ι → Submodule 𝕜 E) :
    B.polarSubmodule (⨆ i, U i) = ⨅ i, B.polarSubmodule (U i) :=
  (polarSubmodule_gc B).l_iSup

theorem polarSubmodule_sup_le_inf (U V : Submodule 𝕜 E) :
    B.polarSubmodule U ⊔ B.polarSubmodule V ≤ B.polarSubmodule (U ⊓ V) :=
  sup_le (polarSubmodule_anti inf_le_left) (polarSubmodule_anti inf_le_right)

theorem iSup_polarSubmodule_le_iInf {ι : Sort*} (U : ι → Submodule 𝕜 E) :
    ⨆ i, B.polarSubmodule (U i) ≤ B.polarSubmodule (⨅ i, U i) :=
  iSup_le fun i ↦ polarSubmodule_anti (iInf_le U i)

/-- The polar of the `Submodule.span` of a set `s` consists of those `y` such that `B x y = 0` for
all `x ∈ s`. -/
@[simp]
theorem coe_polarSubmodule_span (s : Set E) :
    (B.polarSubmodule (span 𝕜 s) : Set F) = {y | ∀ x ∈ s, B x y = 0} := by
  ext y
  simp only [SetLike.mem_coe, mem_polarSubmodule, Set.mem_ofPred_eq]
  exact span_le (p := ker (B.flip y))

theorem polarSubmodule_span (s : Set E) :
    B.polarSubmodule (span 𝕜 s) = ⨅ x ∈ s, ker (B x) := by
  simp [SetLike.ext'_iff, Set.ext_iff]

section Maps

variable {E' F' : Type*} [AddCommMonoid E'] [Module 𝕜 E'] [AddCommMonoid F'] [Module 𝕜 F']

variable (B) in
/-- The polar of the range of `f` is the kernel of `(B ∘ₗ f).flip`. -/
theorem polarSubmodule_range (f : E' →ₗ[𝕜] E) :
    B.polarSubmodule (range f) = ker (B ∘ₗ f).flip := by
  ext y
  simp [LinearMap.ext_iff]

/-- If `g` is adjoint to `f` relative to the bilinear forms `B` and `B'` (i.e.,
`B' (f x) y = B x (g y)`), then the range of `g` is contained in the polar of the kernel of `f`.

The hypothesis is stated in the form of the right-hand side of
`LinearMap.isAdjointPair_iff_comp_eq_compl₂`, since `LinearMap.IsAdjointPair` currently requires
both bilinear forms to take their two arguments from the same module. -/
theorem range_le_polarSubmodule_ker {B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜} {f : E →ₗ[𝕜] E'}
    {g : F' →ₗ[𝕜] F} (hfg : B' ∘ₗ f = B.compl₂ g) :
    range g ≤ B.polarSubmodule (ker f) := by
  rintro _ ⟨y, rfl⟩
  simp +contextual [← compl₂_apply, ← hfg]

end Maps

section Topology

variable [TopologicalSpace F]

variable (B) in
/-- The polar of a submodule is closed if each `B x` is continuous. -/
theorem isClosed_polarSubmodule_of_continuous (hB : ∀ x, Continuous (B x)) {S : Type*}
    [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : IsClosed (B.polarSubmodule m : Set F) := by
  simp only [polarSubmodule_eq_biInf, coe_iInf]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage (hB x)

variable (B) in
/-- The polar of a submodule is closed in the weak topology induced by `B.flip`. -/
theorem isClosed_polarSubmodule [B.flip.IsWeak] {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E]
    (m : S) : IsClosed (B.polarSubmodule m : Set F) :=
  B.isClosed_polar m

variable [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]

theorem topologicalClosure_le_polarSubmodule (hB : ∀ x, Continuous (B x)) {W : Submodule 𝕜 E}
    {Φ : Submodule 𝕜 F} (h : Φ ≤ B.polarSubmodule W) :
    Φ.topologicalClosure ≤ B.polarSubmodule W :=
  Φ.topologicalClosure_minimal h (B.isClosed_polarSubmodule_of_continuous hB W)

@[simp]
theorem flip_polarSubmodule_topologicalClosure (hB : ∀ x, Continuous (B x)) (Φ : Submodule 𝕜 F) :
    B.flip.polarSubmodule Φ.topologicalClosure = B.flip.polarSubmodule Φ :=
  le_antisymm (polarSubmodule_anti Φ.le_topologicalClosure) <| by
    rw [← le_polarSubmodule_iff]
    exact topologicalClosure_le_polarSubmodule hB (le_polarSubmodule_flip_polarSubmodule Φ)

end Topology

end NontriviallyNormedField

/-- The subspace of `E` on which every functional in `m` vanishes is closed. This is an instance
so that, e.g., the quotient by it is a normed space when `E` is. -/
instance _root_.isClosed_topDualPairing_polarSubmodule [NontriviallyNormedField 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] {S : Type*} [SetLike S (StrongDual 𝕜 E)]
    [SMulMemClass S 𝕜 (StrongDual 𝕜 E)] (m : S) :
    IsClosed ((topDualPairing 𝕜 E).polarSubmodule m : Set E) :=
  (topDualPairing 𝕜 E).isClosed_polarSubmodule_of_continuous (fun φ ↦ φ.continuous) m

/-! ### Topologies compatible with `B` -/

namespace IsCompatibleDual

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsCompatibleDual]

/-- If the topology on `E` is compatible with `B`, then `B.flip.polarSubmodule Φ` is closed. -/
theorem isClosed_flip_polarSubmodule {S : Type*} [SetLike S F] [SMulMemClass S 𝕜 F] (m : S) :
    IsClosed (B.flip.polarSubmodule m : Set E) :=
  B.flip.isClosed_polarSubmodule_of_continuous (IsCompatibleDual.continuous B) m

theorem separatingRight : B.SeparatingRight :=
  separatingRight_iff_flip_ker_eq_bot.mpr <| ker_eq_bot.mpr hB.injective

variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

@[simp]
theorem polarSubmodule_topologicalClosure (W : Submodule 𝕜 E) :
    B.polarSubmodule W.topologicalClosure = B.polarSubmodule W := by
  simpa using B.flip.flip_polarSubmodule_topologicalClosure (IsCompatibleDual.continuous B) W

end NontriviallyNormedField

section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [B.IsCompatibleDual]

/-- If `E` is a locally convex space whose topology is compatible with `B`, then the bipolar of a
submodule is its closure. -/
theorem flip_polarSubmodule_polarSubmodule (W : Submodule 𝕜 E) :
    B.flip.polarSubmodule (B.polarSubmodule W) = W.topologicalClosure :=
  SetLike.coe_injective <| by
    rw [coe_polarSubmodule, coe_polarSubmodule, IsCompatibleDual.flip_polar_polar B (s := W)
      ⟨0, W.zero_mem⟩, W.closedAbsConvexHull_eq_topologicalClosure]

theorem flip_polarSubmodule_polarSubmodule_of_isClosed {W : Submodule 𝕜 E}
    (hW : IsClosed (W : Set E)) : B.flip.polarSubmodule (B.polarSubmodule W) = W := by
  rw [flip_polarSubmodule_polarSubmodule, hW.submodule_topologicalClosure_eq]

theorem forall_mem_polarSubmodule_apply_eq_zero_iff (W : Submodule 𝕜 E) (x : E) :
    (∀ y ∈ B.polarSubmodule W, B x y = 0) ↔ x ∈ W.topologicalClosure := by
  rw [← flip_polarSubmodule_polarSubmodule B, mem_polarSubmodule]
  rfl

theorem polarSubmodule_le_polarSubmodule_iff {W W' : Submodule 𝕜 E} :
    B.polarSubmodule W ≤ B.polarSubmodule W' ↔ W' ≤ W.topologicalClosure := by
  rw [le_polarSubmodule_iff, flip_polarSubmodule_polarSubmodule]

theorem polarSubmodule_inj {W W' : Submodule 𝕜 E} :
    B.polarSubmodule W = B.polarSubmodule W' ↔ W.topologicalClosure = W'.topologicalClosure := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← flip_polarSubmodule_polarSubmodule B, h]
  · rw [← polarSubmodule_topologicalClosure B W, h, polarSubmodule_topologicalClosure]

@[simp]
theorem polarSubmodule_eq_bot_iff {W : Submodule 𝕜 E} :
    B.polarSubmodule W = ⊥ ↔ Dense (W : Set E) := by
  rw [← (separatingRight B).polarSubmodule_top, polarSubmodule_inj,
    dense_iff_topologicalClosure_eq_top, top_unique (⊤ : Submodule 𝕜 E).le_topologicalClosure]

theorem polarSubmodule_inf {U V : Submodule 𝕜 E} (hU : IsClosed (U : Set E))
    (hV : IsClosed (V : Set E)) :
    B.polarSubmodule (U ⊓ V) =
      B.polarSubmodule (B.flip.polarSubmodule (B.polarSubmodule U ⊔ B.polarSubmodule V)) := by
  rw [polarSubmodule_sup, flip_polarSubmodule_polarSubmodule_of_isClosed B hU,
    flip_polarSubmodule_polarSubmodule_of_isClosed B hV]

theorem polarSubmodule_iInf {ι : Sort*} {U : ι → Submodule 𝕜 E}
    (hU : ∀ i, IsClosed (U i : Set E)) :
    B.polarSubmodule (⨅ i, U i) =
      B.polarSubmodule (B.flip.polarSubmodule (⨆ i, B.polarSubmodule (U i))) := by
  simp_rw [polarSubmodule_iSup, flip_polarSubmodule_polarSubmodule_of_isClosed B (hU _)]

end RCLike

end IsCompatibleDual

/-! ### The weak topology induced by `B` -/

namespace IsWeak

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [B.IsWeak]

/-- If `E` carries the weak topology induced by `B`, then `B.flip.polarSubmodule Φ` is closed. -/
theorem isClosed_flip_polarSubmodule {S : Type*} [SetLike S F] [SMulMemClass S 𝕜 F] (m : S) :
    IsClosed (B.flip.polarSubmodule m : Set E) :=
  B.flip.isClosed_polarSubmodule m

variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

@[simp]
theorem polarSubmodule_topologicalClosure (W : Submodule 𝕜 E) :
    B.polarSubmodule W.topologicalClosure = B.polarSubmodule W := by
  simpa using B.flip.flip_polarSubmodule_topologicalClosure (IsWeak.continuous_eval B) W

end NontriviallyNormedField

section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
  [B.IsWeak]

/-- If `E` carries the weak topology induced by `B`, then the bipolar of a submodule is its
closure. -/
theorem flip_polarSubmodule_polarSubmodule (W : Submodule 𝕜 E) :
    B.flip.polarSubmodule (B.polarSubmodule W) = W.topologicalClosure :=
  SetLike.coe_injective <| by
    rw [coe_polarSubmodule, coe_polarSubmodule, B.flip_polar_polar (s := W) ⟨0, W.zero_mem⟩,
      W.closedAbsConvexHull_eq_topologicalClosure]

theorem flip_polarSubmodule_polarSubmodule_of_isClosed {W : Submodule 𝕜 E}
    (hW : IsClosed (W : Set E)) : B.flip.polarSubmodule (B.polarSubmodule W) = W := by
  rw [flip_polarSubmodule_polarSubmodule, hW.submodule_topologicalClosure_eq]

theorem forall_mem_polarSubmodule_apply_eq_zero_iff (W : Submodule 𝕜 E) (x : E) :
    (∀ y ∈ B.polarSubmodule W, B x y = 0) ↔ x ∈ W.topologicalClosure := by
  rw [← flip_polarSubmodule_polarSubmodule B, mem_polarSubmodule]
  rfl

theorem polarSubmodule_le_polarSubmodule_iff {W W' : Submodule 𝕜 E} :
    B.polarSubmodule W ≤ B.polarSubmodule W' ↔ W' ≤ W.topologicalClosure := by
  rw [le_polarSubmodule_iff, flip_polarSubmodule_polarSubmodule]

theorem polarSubmodule_inj {W W' : Submodule 𝕜 E} :
    B.polarSubmodule W = B.polarSubmodule W' ↔ W.topologicalClosure = W'.topologicalClosure := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← flip_polarSubmodule_polarSubmodule B, h]
  · rw [← polarSubmodule_topologicalClosure B W, h, polarSubmodule_topologicalClosure]

theorem polarSubmodule_eq_bot_iff (hB : B.SeparatingRight) {W : Submodule 𝕜 E} :
    B.polarSubmodule W = ⊥ ↔ Dense (W : Set E) := by
  rw [← hB.polarSubmodule_top, polarSubmodule_inj, dense_iff_topologicalClosure_eq_top,
    top_unique (⊤ : Submodule 𝕜 E).le_topologicalClosure]

theorem polarSubmodule_inf {U V : Submodule 𝕜 E} (hU : IsClosed (U : Set E))
    (hV : IsClosed (V : Set E)) :
    B.polarSubmodule (U ⊓ V) =
      B.polarSubmodule (B.flip.polarSubmodule (B.polarSubmodule U ⊔ B.polarSubmodule V)) := by
  rw [polarSubmodule_sup, flip_polarSubmodule_polarSubmodule_of_isClosed B hU,
    flip_polarSubmodule_polarSubmodule_of_isClosed B hV]

theorem polarSubmodule_iInf {ι : Sort*} {U : ι → Submodule 𝕜 E}
    (hU : ∀ i, IsClosed (U i : Set E)) :
    B.polarSubmodule (⨅ i, U i) =
      B.polarSubmodule (B.flip.polarSubmodule (⨆ i, B.polarSubmodule (U i))) := by
  simp_rw [polarSubmodule_iSup, flip_polarSubmodule_polarSubmodule_of_isClosed B (hU _)]

end RCLike

end IsWeak

end LinearMap
