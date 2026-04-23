/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import LeanOA.LocallyConvexNhdsBasis
import LeanOA.Mathlib.Analysis.LocallyConvex.Polar
import LeanOA.Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import LeanOA.Mathlib.Analysis.LocallyConvex.IsCompatible
import LeanOA.IsWeak

/-!

# Bipolar Theorem

## Main statements

- `LinearMap.pairing_flip_polar_polar`: The Bipolar Theorem: The bipolar of a set coincides with its
  closed absolutely convex hull.

## References

* [Conway, *A course in functional analysis*][conway1990]

## Tags

bipolar, locally convex space
-/

public section

open scoped ComplexOrder

theorem LocallyConvexSpace.real_iff_rclike (𝕜 E : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [TopologicalSpace E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E ↔ LocallyConvexSpace 𝕜 E := by
  simp only [locallyConvexSpace_iff_exists_convex_subset, convex_RCLike_iff_convex_real]

alias ⟨LocallyConvexSpace.to_rclike, LocallyConvexSpace.to_real⟩ :=
  LocallyConvexSpace.real_iff_rclike

variable {𝕜 E F : Type*}

namespace LinearMap

section

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

/-
When `B` is left-separating, the closure of the empty set is the singleton `{0}`. This is in
contrast to the closed absolutely convex hull of the empty set, which is again the empty set.
c.f. `closureOperator_polar_gc_nonempty` below.
-/
example (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (h : SeparatingLeft B) :
    B.polar_gc.closureOperator (∅ : Set E) = {0} := by
  simp only [GaloisConnection.closureOperator_apply, Function.comp_apply, polar_empty,
    OrderDual.ofDual_toDual, (B.flip.polar_univ h)]

end


section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

alias absConvex_polar := polar_AbsConvex

/-
The **Bipolar Theorem**: The bipolar of a set `s : Set E` relative to a bilinear form
`B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` (where `E` is equipped with the weak topology induced by `B`)
coincides with its closed absolutely convex hull.
[Conway, *A course in functional analysis*, Chapter V. 1.8][conway1990]
-/
open scoped ComplexConjugate ComplexOrder in
theorem flip_polar_polar [TopologicalSpace E] [hB : B.IsWeak] {s : Set E}
    (hs : s.Nonempty) :
    B.flip.polar (B.polar s) = closedAbsConvexHull 𝕜 s := by
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  have _ := hs.to_subtype -- can be removed after issue below is fixed.
  have : IsTopologicalAddGroup E := hB.isTopologicalAddGroup _
  have : LocallyConvexSpace ℝ E := hB.locallyConvexSpace _
  have : ContinuousSMul 𝕜 E := hB.continuousSMul _
  apply subset_antisymm ?h1 <| closedAbsConvexHull_min (subset_bipolar B s)
      (absConvex_polar _) (B.flip.isClosed_polar _)
  rw [← Set.compl_subset_compl]
  -- Let `x` be an element not in `(closedAbsConvexHull 𝕜) s`
  intro x hx
  obtain ⟨f, ⟨u, ⟨hf₁, hf₂⟩⟩⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (by rw [← convex_RCLike_iff_convex_real (K := 𝕜)]; exact absConvex_convexClosedHull.2)
      isClosed_closedAbsConvexHull hx
  -- `0` is in `(closedAbsConvexHull 𝕜) s` so `u` must be strictly positive
  have f_zero_lt_u : RCLike.re (f 0) < u :=
    (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
     --zero_mem_absConvexyHull needs coercion to subtype, which should be fixed in Mathlib.
  rw [map_zero, map_zero] at f_zero_lt_u
  -- Rescale `f` as `g` in order that for all `a` in `(closedAbsConvexHull 𝕜) s` `Re (g a) < 1`
  set g := (1/u : ℝ) • f with fg
  have u_smul_g_eq_f : u • g = f := by
    rw [fg, one_div, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (ne_of_lt f_zero_lt_u).symm,
      one_smul]
  have re_g_a_lt_one {a : _} (ha : a ∈ closedAbsConvexHull 𝕜 s) :
    RCLike.re (g a) < 1 := by
    rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
      ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp f_zero_lt_u).2.symm)]
    exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos f_zero_lt_u)
  -- The dual embedding is surjective, let `f₀` be the element of `F` corresponding to `g`
  obtain ⟨f₀, hf₀⟩ := hB.eval_surjective _ g
  -- Then, by construction, `f₀` is in the polar of `s`
  have mem_polar : f₀ ∈ B.polar s := by
    simp only [← hf₀, LinearMap.IsWeak.eval, coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk']
      at re_g_a_lt_one
    intro x₂ hx₂
    let l := conj (B x₂ f₀) / ‖B x₂ f₀‖
    have lnorm : ‖l‖ ≤ 1 := by
      rw [norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm]
      exact div_self_le_one _
    have i1 : RCLike.re ((B.flip f₀) (l • x₂)) ≤ 1 := le_of_lt <| re_g_a_lt_one
      <| balanced_iff_smul_mem.mp absConvex_convexClosedHull.1 lnorm
        (subset_closedAbsConvexHull hx₂)
    rwa [CompatibleSMul.map_smul, smul_eq_mul, mul_comm, ← mul_div_assoc, LinearMap.flip_apply,
      RCLike.mul_conj, sq, mul_self_div_self, RCLike.ofReal_re] at i1
  -- and `1 < Re (B x f₀)`
  have one_lt_x_f₀ : 1 < RCLike.re (B x f₀) := by
    rw [← one_lt_inv_mul₀ f_zero_lt_u] at hf₂
    suffices u⁻¹ * RCLike.re (f x) = RCLike.re (B x f₀) by exact lt_of_lt_of_eq hf₂ this
    rw [← RCLike.re_ofReal_mul]
    congr
    simp only [map_inv₀, ← u_smul_g_eq_f, ← hf₀, LinearMap.IsWeak.eval, coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_mk', Pi.smul_apply,
      Algebra.mul_smul_comm]
    rw [← smul_eq_mul, ← smul_assoc]
    norm_cast
    simp only [smul_eq_mul, mul_inv_cancel₀ (ne_of_lt f_zero_lt_u).symm, map_one, one_mul]
    exact flip_apply ..
  -- From which it follows that `x` can't be in the bipolar of `s`
  exact fun hc ↦ ((lt_iff_le_not_ge.mp one_lt_x_f₀).2)
    (Preorder.le_trans (RCLike.re (B x f₀)) ‖B x f₀‖ 1
      (RCLike.re_le_norm (B x f₀)) (hc f₀ mem_polar))

alias bipolar := flip_polar_polar

/-
set_option backward.isDefEq.respectTransparency false in
open scoped ComplexConjugate ComplexOrder in
theorem _root_.StrongDual.topDualPairing_flip_polar_polar
    [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] {s : Set E} [h : Nonempty s] :
    (topDualPairing 𝕜 E).polar ((topDualPairing 𝕜 E).flip.polar s)
      = closedAbsConvexHull 𝕜 s := by
  have := pairing_flip_polar_polar (topDualPairing 𝕜 E).flip
    (s :=(((WeakBilin.linearEquiv 𝕜 (topDualPairing 𝕜 E).flip).symm '' s)))
  have := congr (WeakSpace.weakBilinCLE)
  sorry
-/

--Convex.toWeakSpace_closure
--Map the bipolar here through WeakSpace, and we get the above bipolar.
--Convex set is closed iff image is closed under toWeakSpace. (Prove lemma.)

/-
This fails when `s` is empty. Indeed, `closedAbsConvexHull (E := WeakBilin B) 𝕜 s` is the empty set,
but `B.polar_gc.closureOperator s` equals `{0}` when `B` is left separating (see example above).
-/
lemma closureOperator_polar_gc_nonempty {s : Set (WeakBilin B)} (hs : s.Nonempty) :
    (WeakBilin.pairing B).polar_gc.closureOperator s = closedAbsConvexHull 𝕜 s := by
  simp [(WeakBilin.pairing B).flip_polar_polar hs]

end RCLike

end LinearMap

set_option backward.isDefEq.respectTransparency false in
open ComplexOrder in
theorem toWeakSpace_closedAbsConvexHull_eq {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedAbsConvexHull 𝕜 s) = closedAbsConvexHull 𝕜 (toWeakSpace 𝕜 E '' s)
    := by
  simpa only [← closedAbsConvexHull_eq_closedConvexHull_balancedHull, LinearEquiv.coe_coe,
    ← toWeakSpace_closedConvexHull_eq] using
    congr(closedConvexHull 𝕜 $((toWeakSpace 𝕜 E).image_balancedHull s))

theorem Convex.toWeakSpace_symm_closure (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set (WeakSpace 𝕜 E)} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E).symm '' closure s = closure ((toWeakSpace 𝕜 E).symm '' s) := by
  apply (toWeakSpace 𝕜 E).injective.image_injective
  trans closure (toWeakSpace 𝕜 E '' ((toWeakSpace 𝕜 E).symm '' s))
  · simp [Set.image_image]
  · rw [Convex.toWeakSpace_closure]
    exact hs.linear_image <| (toWeakSpace 𝕜 E).symm.toLinearMap.restrictScalars ℝ

open ComplexOrder in
theorem toWeakSpace_symm_closedConvexHull_eq {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set (WeakSpace 𝕜 E)} :
    (toWeakSpace 𝕜 E).symm '' (closedConvexHull 𝕜 s) =
      closedConvexHull 𝕜 ((toWeakSpace 𝕜 E).symm '' s) := by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜),
    ((convex_convexHull 𝕜 s).lift ℝ).toWeakSpace_symm_closure _,
      closedConvexHull_eq_closure_convexHull]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).symm.toLinearMap s

open ComplexOrder in
theorem toWeakSpace_symm_closedAbsConvexHull_eq {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set (WeakSpace 𝕜 E)} :
    (toWeakSpace 𝕜 E).symm '' (closedAbsConvexHull 𝕜 s) =
      closedAbsConvexHull 𝕜 ((toWeakSpace 𝕜 E).symm '' s)
    := by
  simpa [closedAbsConvexHull_eq_closedConvexHull_balancedHull,
    toWeakSpace_symm_closedConvexHull_eq] using
      congr(closedConvexHull 𝕜 $((toWeakSpace 𝕜 E).symm.image_balancedHull s))

open ComplexOrder in
theorem _root_.ContinuousLinearEquiv.closedAbsConvexHull_image {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F]
    {s : Set E} (f : E ≃L[𝕜] F) :
    f '' (closedAbsConvexHull 𝕜 s) = closedAbsConvexHull 𝕜 (f '' s)
    := by
  rw [closedAbsConvexHull_eq_closedConvexHull_balancedHull, closedConvexHull_eq_closure_convexHull,
    ContinuousLinearEquiv.image_closure, ← absConvexHull_eq_convexHull_balancedHull,
     ← ContinuousLinearEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_coe,
     LinearMap.image_absConvexHull, ← closedAbsConvexHull_eq_closure_absConvexHull]

open scoped ComplexConjugate ComplexOrder in
theorem _root_.StrongDual.topDualPairing_flip_polar_polar (𝕜 : Type*) {E : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] {s : Set E} (h : s.Nonempty) :
    (topDualPairing 𝕜 E).polar ((topDualPairing 𝕜 E).flip.polar s) = closedAbsConvexHull 𝕜 s := by
  have := congr(toWeakSpace 𝕜 E ⁻¹' $((weakSpacePairing 𝕜 E).bipolar (h.image (toWeakSpace 𝕜 E))))
  rw [← toWeakSpace_closedAbsConvexHull_eq] at this
  simpa [LinearEquiv.image_eq_preimage_symm]

open LinearMap

alias StrongDual.bipolar := StrongDual.topDualPairing_flip_polar_polar

set_option backward.isDefEq.respectTransparency false in
open scoped ComplexConjugate ComplexOrder in
theorem LinearMap.IsCompatible.flip_polar_polar {𝕜 E F : Type*}
    [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    [AddCommGroup F] [Module 𝕜 F]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsCompatible] {s : Set E} (h : s.Nonempty) :
    B.flip.polar (B.polar s) = closedAbsConvexHull 𝕜 s := by
  convert StrongDual.topDualPairing_flip_polar_polar 𝕜 h
  ext
  simp [polar_mem_iff, (IsCompatible.equiv B).surjective.forall]

alias LinearMap.IsCompatible.bipolar := LinearMap.IsCompatible.flip_polar_polar
