module

public import LeanOA.Mathlib.Topology.Algebra.Module.PolarTopology

@[expose] public section

open scoped ComplexOrder
open WeakBilin

open Set Filter Bornology

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [TopologicalSpace F]

/-- The Mackey toplogy on a space `E` relative to a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is the
polar topology corresponding to all (weakly) compact absolutely convex sets in `F`.

Although it is not required for the definition, the space `F` should be equipped with the weak
topology induced by `B.flip` for any of the usual theorems to be applicable. -/
abbrev Mackey (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :=
    PolarTopology B {s | IsCompact s ∧ AbsConvex 𝕜 s}

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

variable (B) in
/-- The identity map from `E` to its type synonym equipped with the Mackey topology. -/
noncomputable def toMackey : E ≃ₗ[𝕜] Mackey B := PolarTopology.linearEquiv.symm

/-- The identity map from the type synonrm `Mackey B` back to `E` with its original topology. -/
noncomputable def ofMackey : Mackey B ≃ₗ[𝕜] E := PolarTopology.linearEquiv

@[simp]
lemma ofMackey_symm : ofMackey.symm = toMackey B := rfl

@[simp]
lemma toMackey_symm : (toMackey B).symm = ofMackey := rfl

@[simp]
lemma toMackey_ofMackey (x : Mackey B) : toMackey B (ofMackey x) = x := rfl

@[simp]
lemma ofMackey_toMackey (x : E) : ofMackey (toMackey B x) = x := rfl

theorem nonempty_setOf_isCompact_absConvex (𝕜 F : Type*) [NormedField 𝕜]
    [PartialOrder 𝕜] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] :
    (Set.Nonempty {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s}) :=
  ⟨∅, isCompact_empty, .empty⟩

theorem directedOn_setOf_isCompact_absConvex (𝕜 F : Type*) [RCLike 𝕜]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [T2Space F] :
    DirectedOn (· ⊆ ·) {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s} := by
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  refine ⟨closedAbsConvexHull 𝕜 (convexHull 𝕜 (s ∪ t)), ⟨?_, absConvex_convexClosedHull⟩,
    ?hs, ?ht⟩
  case hs | ht => grw [← subset_closedAbsConvexHull, ← subset_convexHull]; simp
  exact hs₁.convexHull_union ht₁ hs₂.2 ht₂.2 |>.closedAbsConvexHull (convex_convexHull 𝕜 _)

namespace Mackey

/-- This version assumes `B.IsWeak` and is only meant to be used in developing the API for
`Mackey`. -/
theorem _root_.IsCompact.isVonNBounded' {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [B.IsWeak] {s : Set E} (hs : IsCompact s) :
    IsVonNBounded 𝕜 s :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B
  have := LinearMap.IsWeak.continuousSMul B
  hs.isVonNBounded 𝕜

variable (B)
variable [B.flip.IsWeak]

-- can we eliminate the need for `T2Space F` here? At least under certain circumstances?
-- probably `IsCompatible` will be enough? This was used in the proof that the
-- `closedAbsConvexHull` of a compact convex set is compact. I'm unsure if it's strictly necessary
-- there.
instance [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [T2Space F] :
    LocallyConvexSpace ℝ (Mackey B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.locallyConvexSpace (nonempty_setOf_isCompact_absConvex 𝕜 _)
    (directedOn_setOf_isCompact_absConvex 𝕜 _) fun _ h ↦ h.1.isVonNBounded' B.flip

instance [T2Space F] : LocallyConvexSpace 𝕜 (Mackey B) :=
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  .to_rclike 𝕜 (Mackey B) inferInstance

/-- Every compact set gives rise to a seminorm on `Mackey B`, but in practice we are only interested
in those for which the sets are also absolutely convex. -/
noncomputable abbrev seminorm (s : Set F) (hs : IsCompact s) :
    Seminorm 𝕜 (Mackey B) :=
  PolarTopology.seminorm B {s | IsCompact s ∧ AbsConvex 𝕜 s} s <| hs.isVonNBounded' B.flip

/-- The compact absolutely convex sets give rise to a seminorm family on `Mackey B` which induces
the topology. -/
noncomputable abbrev seminormFamily :
    SeminormFamily 𝕜 (Mackey B) {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s} :=
  PolarTopology.seminormFamily B {s | IsCompact s ∧ AbsConvex 𝕜 s}
    fun _s hs ↦ hs.1.isVonNBounded' B.flip

lemma continuous_seminorm [T2Space F] (s : Set F) (hs₁ : IsCompact s) (hs₂ : AbsConvex 𝕜 s) :
    Continuous (seminorm B s hs₁) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.continuous_seminorm (nonempty_setOf_isCompact_absConvex 𝕜 F)
    (directedOn_setOf_isCompact_absConvex 𝕜 F) _ ⟨hs₁, hs₂⟩ (hs₁.isVonNBounded' B.flip)

lemma directed_seminormFamily [T2Space F] : Directed (· ≤ ·) (seminormFamily B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.directed_seminormFamily (fun _s hs ↦ hs.1.isVonNBounded' B.flip)
    (directedOn_setOf_isCompact_absConvex 𝕜 F)

lemma withSeminorms [T2Space F] : WithSeminorms (seminormFamily B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.withSeminorms B _ (nonempty_setOf_isCompact_absConvex 𝕜 F)
    (directedOn_setOf_isCompact_absConvex 𝕜 F) fun _s hs ↦ hs.1.isVonNBounded' B.flip

end Mackey

variable (B)
variable [B.flip.IsWeak]

open PolarTopology in
/-- Every compatible locally convex topology is weaker than the Mackey topology. -/
lemma continuous_ofMackey [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] [B.IsCompatible] :
    Continuous (ofMackey : Mackey B → E) := by
  refine polarTopologyNhdsPolars.continuous.comp <|
    continuous_mono B B.nhdsPolars {s | IsCompact s ∧ AbsConvex 𝕜 s} ?_
  rintro - ⟨s, hs, rfl⟩
  exact ⟨LinearMap.IsCompatible.isCompact_polar B hs, B.absConvex_polar s⟩

/-- The map `⇑ofMackey : Mackey 𝕜 E → E` as a continuous linear map. -/
noncomputable def ofMackeyCLM [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] [B.IsCompatible] :
    Mackey B →L[𝕜] E where
  toLinearMap := ofMackey.toLinearMap
  cont := continuous_ofMackey B

open PolarTopology in
theorem isWeak_bilin :
    (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).IsWeak := by
  apply LinearMap.IsWeak.congr B.flip (e := ContinuousLinearEquiv.refl 𝕜 F) (f := toMackey B)
  aesop

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
set_option linter.unusedSectionVars false in
theorem Mackey.range_coeLM_eq_image_bilin [IsTopologicalAddGroup F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [T1Space F] [ContinuousSMul 𝕜 F] :
    (coeLM 𝕜 : StrongDual 𝕜 (Mackey B) →ₗ[𝕜] Dual 𝕜 (Mackey B)).range =
      (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}) '' univ := by
  letI B₁ := bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  have : ContinuousSMul 𝕜 (Mackey B) := by
    apply PolarTopology.continuousSMul (E := Mackey B)
    exact fun _ hS ↦ IsCompact.isVonNBounded 𝕜 hS.1
  have := isWeak_bilin B
  rw [StrongDual.range_coeLM_eq_sUnion_polar_nhds <|
      hasBasis_nhds_zero_polar (nonempty_setOf_isCompact_absConvex _ _)
        (directedOn_setOf_isCompact_absConvex _ _)
        (by simpa [mem_setOf_eq, and_imp] using fun _ h _ ↦ IsCompact.isVonNBounded _ h)
        (fun c _ w hw ↦ ⟨c • w, ⟨⟨IsCompact.smul _ hw.1, by
                simpa using AbsConvex.image (Module.End.smulLeft (RCLike.ofReal _)
                  (algebraMap_mem_center _)) hw.2⟩, by aesop⟩⟩)]
  ext x
  constructor
  · simp only [mem_setOf_eq, exists_prop, mem_sUnion, exists_exists_and_eq_and]
    rintro ⟨s, _, hb⟩
    by_cases hne : s.Nonempty
    · rw [Module.dualPairing_flip_polar_polar B₁ (by aesop) (by aesop) hne] at hb
      grind
    · simp only [image_univ, mem_range, not_nonempty_iff_eq_empty.mp hne , polar_empty] at hb ⊢
      rw [polar_univ, mem_singleton_iff] at hb
      · use 0; rw [hb, map_zero]
      exact separatingRight_iff_flip_ker_eq_bot.mpr rfl
  · simp only [image_univ, mem_range, mem_setOf_eq, exists_prop, mem_sUnion,
    exists_exists_and_eq_and, forall_exists_index]
    intro f hf
    use closedAbsConvexHull 𝕜 (convexHull ℝ {f})
    have hcpt : IsCompact <| closedAbsConvexHull 𝕜 (convexHull ℝ {f}) := by
      apply IsCompact.closedAbsConvexHull <| Set.Finite.isCompact_convexHull _
        Finite.of_subsingleton
      rw [← convexHull_rclike_eq_convexHull_real (K := 𝕜)]
      exact convex_convexHull ..
    exact ⟨⟨hcpt, absConvex_convexClosedHull⟩, by
      rw [Module.dualPairing_flip_polar_polar B₁ absConvex_convexClosedHull hcpt
        (by simp [convexHull_singleton, closedAbsConvexHull_eq_closure_absConvexHull,
         closure_nonempty_iff, absConvexHull_nonempty, singleton_nonempty])]
      exact ⟨f, by simpa [closedAbsConvexHull_eq_closure_absConvexHull] using subset_closure <|
           (mem_absConvexHull_iff.mpr fun _ a _ ↦ a rfl : f ∈ absConvexHull 𝕜 {_}), hf⟩⟩

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
set_option linter.unusedSectionVars false in
theorem Mackey.range_coeLM_eq_range_bilin [IsTopologicalAddGroup F] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 F] [T1Space F] [ContinuousSMul 𝕜 F] :
    (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).range =
      (coeLM 𝕜 : StrongDual 𝕜 (Mackey B) →ₗ[𝕜] Dual 𝕜 (Mackey B)).range := by
  have : (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).range =
      (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}) '' univ := by
    ext; simp
  have h2 := Mackey.range_coeLM_eq_image_bilin B
  rw [← this] at h2
  exact_mod_cast h2.symm

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
/-- The topology on `Mackey B` is compatible with the type-appropriate version of `B`. -/
instance [IsTopologicalAddGroup F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [T1Space F]
    [ContinuousSMul 𝕜 F] : (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).flip.IsCompatible where
  range_eq_range := Mackey.range_coeLM_eq_range_bilin B
  injective := by
    rw [LinearMap.flip_flip, ← LinearMap.ker_eq_bot]
    ext x
    constructor
    · intro hx
      simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
        LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, LinearEquiv.refl_apply,
        LinearMap.zero_apply, Submodule.mem_bot] at hx ⊢
      apply (flip_separatingLeft.mp <| IsWeak.separatingLeft_of_t1Space B.flip) x
      exact fun _ ↦ isOrtho_def.mp (hx _)
    · intro hx
      simp at hx
      aesop
