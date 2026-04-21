import Mathlib.Analysis.LocallyConvex.AbsConvex

open Set

lemma closedAbsConvexHull_eq_closedConvexHull_balancedHull
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s : Set E} :
    closedAbsConvexHull 𝕜 s = closedConvexHull 𝕜 (balancedHull 𝕜 s) := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull, absConvexHull_eq_convexHull_balancedHull,
    closedConvexHull_eq_closure_convexHull]

theorem LinearMap.image_balancedHull {𝕜 E F : Type*} [SeminormedRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (f : E →ₗ[𝕜] F) (s : Set E) :
    f '' balancedHull 𝕜 s = balancedHull 𝕜 (f '' s) := by
  ext x
  simp only [mem_balancedHull_iff, mem_image]
  -- I want there to be a simpler proof of this
  constructor
  · rintro ⟨-, ⟨r, hr, ⟨x, hx, rfl⟩⟩, rfl⟩
    exact ⟨r, hr, ⟨f x, ⟨x, hx, rfl⟩, by simp⟩⟩
  · rintro ⟨r, hr, ⟨-, ⟨x, hx, rfl⟩, rfl⟩⟩
    exact ⟨r • x, ⟨r, hr, ⟨x, hx, rfl⟩⟩, by simp⟩

theorem LinearMap.image_absConvexHull {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (f : E →ₗ[𝕜] F) (s : Set E) :
    f '' absConvexHull 𝕜 s = absConvexHull 𝕜 (f '' s):= by
  rw [absConvexHull_eq_convexHull_balancedHull, image_convexHull, image_balancedHull,
    absConvexHull_eq_convexHull_balancedHull]

theorem AbsConvex.image {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (f : E →ₗ[𝕜] F) {s : Set E}
    (hs : AbsConvex 𝕜 s) :
    AbsConvex 𝕜 (f '' s) := by
  rw [← hs.absConvexHull_eq, f.image_absConvexHull]
  exact absConvex_absConvexHull

open AffineMap in
-- this can be generalized in Mathlib
theorem Convex.closure_subset_image_homothety_interior_of_one_lt'
    {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
    [IsOrderedRing 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : Convex 𝕜 s)
    {x : E} (hx : x ∈ interior s) (t : 𝕜) (ht : 1 < t) :
    closure s ⊆ homothety x t '' interior s := by
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [homothety_eq_lineMap]
  exact lineMap_mem_openSegment _ _ _ ⟨inv_pos_of_pos (by grind), inv_lt_one_of_one_lt₀ (by grind)⟩

theorem AffineMap.bijective_homothety {R V P : Type*} [AddCommGroup V] [TopologicalSpace V]
    [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P] [Field R] [Module R V]
    [ContinuousConstSMul R V] (x : P) (t : R) (ht : t ≠ 0) :
    Function.Bijective (AffineMap.homothety x t) := by
  lift t to Rˣ using IsUnit.mk0 t ht
  exact AffineEquiv.homothetyUnitsMulHom x t |>.bijective

theorem AffineMap.isHomeomorph_homothety {R V P : Type*} [AddCommGroup V] [TopologicalSpace V]
    [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P] [Field R] [Module R V]
    [ContinuousConstSMul R V] (x : P) (t : R) (ht : t ≠ 0) :
    IsHomeomorph (AffineMap.homothety x t) where
  continuous := homothety_continuous x t
  isOpenMap := homothety_isOpenMap x t ht
  bijective := bijective_homothety x t ht

open AffineMap in
theorem Convex.closure_image_homothety_subset_interior_of_lt_one
    {𝕜 E : Type*} [NormedField 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : Convex 𝕜 s) {x : E} (hx : x ∈ interior s)
    (t : 𝕜) (ht₀ : 0 < t) (ht : t < 1) :
    closure (homothety x t '' s) ⊆ interior s := by
  -- this proof is far too much work. There are several missing lemmas around homotheties
  -- I think, even though I already added some. We also don't have them as a
  -- `ContinuousAffineEquiv`, which should have helped.
  lift t to 𝕜ˣ using IsUnit.mk0 t ht₀.ne'
  have ht₁ : (1 : 𝕜) < ↑(t⁻¹) := by simpa using (one_lt_inv₀ ht₀).mpr ht
  have := hs.affine_image (homothety x (t : 𝕜))
  have h_int : interior (homothety x (t : 𝕜) '' s) = homothety x (t : 𝕜) '' interior s :=
    isHomeomorph_homothety x _ ht₀.ne' |>.homeomorph.image_interior _ |>.symm
  have := this.closure_subset_image_homothety_interior_of_one_lt'
    (x := x) (h_int ▸ ⟨x, hx, by simp⟩) _ ht₁
  grw [this, h_int, Set.image_image]
  simp_rw [← AffineEquiv.coe_homothetyUnitsMulHom_apply, ← AffineEquiv.trans_apply,
    ← AffineEquiv.mul_def, ← map_mul]
  simp

open scoped Topology in
open AffineMap in
theorem LocallyConvexSpace.convex_closed_basis_zero (𝕜 E : Type*)
    [NormedField 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E ↦ s ∈ 𝓝 0 ∧ Convex 𝕜 s ∧ IsClosed s) id := by
  simp_rw [← and_assoc]
  apply LocallyConvexSpace.convex_basis_zero 𝕜 E |>.restrict
  rintro s ⟨hs_mem, hs⟩
  refine ⟨closure (homothety 0 (2⁻¹ : 𝕜) '' s), ⟨?_, (hs.affine_image _).closure⟩,
    isClosed_closure, ?_⟩
  · apply Filter.mem_of_superset ?_ subset_closure
    have := (homothety_isOpenMap (0 : E) (2⁻¹ : 𝕜) (by grind)).image_mem_nhds (s := s)
      (by simpa using hs_mem)
    simpa
  · simp only [id_eq]
    exact hs.closure_image_homothety_subset_interior_of_lt_one
      (by simpa [mem_interior_iff_mem_nhds] using hs_mem) (2⁻¹ : 𝕜) (by positivity) (by norm_num)
      |>.trans<| interior_subset

open scoped Topology in
open AffineMap in
theorem LocallyConvexSpace.absConvex_closed_basis_zero (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E ↦ s ∈ 𝓝 0 ∧ AbsConvex 𝕜 s ∧ IsClosed s) id := by
  simp_rw [← and_assoc]
  apply nhds_hasBasis_absConvex 𝕜 E |>.restrict
  rintro s ⟨hs_mem, hs⟩
  refine ⟨closure (homothety 0 (2⁻¹ : 𝕜) '' s), ⟨?_, ?_⟩,
    isClosed_closure, ?_⟩
  · apply Filter.mem_of_superset ?_ subset_closure
    have := (homothety_isOpenMap (0 : E) (2⁻¹ : 𝕜) (by grind)).image_mem_nhds (s := s)
      (by simpa using hs_mem)
    simpa
  · apply AbsConvex.closure
    rw [decomp, homothety_apply_same, ← Pi.zero_def, add_zero]
    exact hs.image _
  · simp only [id_eq]
    exact hs.2.closure_image_homothety_subset_interior_of_lt_one
      (by simpa [mem_interior_iff_mem_nhds] using hs_mem) (2⁻¹ : 𝕜) (by positivity) (by norm_num)
      |>.trans<| interior_subset

#min_imports
