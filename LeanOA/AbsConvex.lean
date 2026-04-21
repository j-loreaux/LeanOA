import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.RCLike.Lemmas

open scoped ComplexOrder
open Set

lemma convexJoin_eq_image {E : Type*} [AddCommGroup E] [Module ℝ E] {s t : Set E} :
    convexJoin ℝ s t = (fun x : E × E × ℝ × ℝ => x.2.2.1 • x.1 + x.2.2.2 • x.2.1) ''
      (s ×ˢ t ×ˢ ({x : ℝ × ℝ | x.1 + x.2 = 1} ∩ (Icc 0 1 ×ˢ Icc 0 1))) := by
  ext x
  simp [mem_convexJoin, segment]
  grind

lemma convexHull_rclike_eq_convexHull_real
    {K E : Type*} [RCLike K] [AddCommMonoid E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    {s : Set E} : convexHull K s = convexHull ℝ s := by
  simp only [convexHull]
  congr!
  funext
  rw [convex_RCLike_iff_convex_real]

lemma IsCompact.convexHull_union {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) (hs' : Convex 𝕜 s) (ht' : Convex 𝕜 t) :
    IsCompact (convexHull 𝕜 (s ∪ t)) := by
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  have _ : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  rw [convexHull_rclike_eq_convexHull_real]
  rw [convex_RCLike_iff_convex_real] at hs' ht'
  obtain (rfl | hs_non) := s.eq_empty_or_nonempty; · simpa [ht'.convexHull_eq]
  obtain (rfl | ht_non) := t.eq_empty_or_nonempty; · simpa [hs'.convexHull_eq]
  rw [hs'.convexHull_union ht' hs_non ht_non, convexJoin_eq_image]
  apply IsCompact.image ?_ (by fun_prop)
  exact hs.prod <| ht.prod <| (isCompact_Icc.prod isCompact_Icc).inter_left <| isClosed_eq
    (by fun_prop)  (by fun_prop)

lemma IsCompact.convexHull_biUnion {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {S : Set (Set E)} (hS_fin : S.Finite) (hS : ∀ s ∈ S, IsCompact s) (hS' : ∀ s ∈ S, Convex 𝕜 s) :
    IsCompact (convexHull 𝕜 (⋃₀ (S : Set (Set E)))) := by
  induction S, hS_fin using Set.Finite.induction_on with
  | empty => simp
  | @insert t S ht hS_fin ih =>
    rw [sUnion_insert]
    suffices convexHull 𝕜 (t ∪ ⋃₀ S) = convexHull 𝕜 (t ∪ convexHull 𝕜 (⋃₀ S)) by
      rw [this]
      apply IsCompact.convexHull_union ?_ (ih ?_ ?_) ?_ (convex_convexHull ..)
      all_goals grind
    apply subset_antisymm
    · gcongr
      exact subset_convexHull ..
    · apply convexHull_min ?_ (convex_convexHull ..)
      apply Set.union_subset
      · exact Set.Subset.trans (by grind) (subset_convexHull ..)
      · gcongr
        grind

/-- Pointwise repeated addition of a convex set is the same as repeated pointwise addition. -/
lemma Convex.nsmul_eq_smul_set {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [PartialOrder 𝕜] [IsOrderedRing 𝕜] [PosMulReflectLT 𝕜] {s : Set E}
    (hs : Convex 𝕜 s) (n : ℕ)
    (hn : n ≠ 0) :
    (letI := Set.NSMul (α := E); n • s) = (letI := Set.smulSet (α := ℕ) (β := E); n • s) := by
  replace hn : 1 ≤ n := by grind
  change _ = _ '' _
  open scoped Pointwise in
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    apply subset_antisymm
    · grw [Set.nsmul_subset_nsmul_add_of_sq_subset_add le_rfl (by simp)]
      simp only [add_tsub_cancel_right, nsmulRec, zero_add, image_smul]
      rw [ih]
      rintro - ⟨-, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
      simp only
      refine ⟨(n + 1 : 𝕜)⁻¹ • n • x + (n + 1 : 𝕜)⁻¹ • y, ?_, ?_⟩
      · rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
        refine convex_iff_add_mem.mp hs hx hy (by positivity) (by positivity) ?_
        field_simp
      · simp [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, ← mul_assoc]
        field_simp
        simp
    · rintro - ⟨x, hx, rfl⟩
      exact ⟨n • x, (ih ▸ ⟨x, hx, rfl⟩ : n • x ∈ n • s), x, hx, by simp [add_smul]⟩

open RCLike Pointwise in
lemma RCLike.closedBall_subset_two_smul_convexHull (𝕜 : Type*) [RCLike 𝕜] :
    Metric.closedBall (0 : 𝕜) 1 ⊆ 2 • convexHull ℝ ({-1, 1, -I, I} : Set 𝕜) := by
  set s := convexHull ℝ ({-1, 1, -I, I} : Set 𝕜)
  have h₁ : segment ℝ (-1) 1 ⊆ s := segment_subset_convexHull (by simp) (by simp)
  have h₂ : segment ℝ (-I) I ⊆ s := segment_subset_convexHull (by simp) (by simp)
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  let a := re x
  let b := im x
  have ha : (a : 𝕜) ∈ s := by
    apply h₁
    have ha' : |a| ≤ 1 := abs_re_le_norm x |>.trans hx
    have ha'' : a ∈ segment ℝ (-1) 1 := by simpa [abs_le] using ha'
    let f := RCLike.ofRealCLM (K := 𝕜) |>.toLinearMap.toAffineMap
    have ha''' : f a ∈ f '' segment ℝ (-1) 1 := ⟨a, ha'', rfl⟩
    simp only [image_segment] at ha'''
    simpa [f] using ha'''
  have hb : (b * I : 𝕜) ∈ s := by
    sorry
  exact ⟨(a : 𝕜), by simpa [nsmulRec] using ha, (b * I : 𝕜), hb, by simp [a, b]⟩

open RCLike Pointwise in
protected lemma IsCompact.closedAbsConvexHull {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    {s : Set E} (hs : IsCompact s) (hs_conv : Convex 𝕜 s) :
    IsCompact (closedAbsConvexHull 𝕜 s) := by
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  have _ : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have : balancedHull 𝕜 s ⊆ 2 • convexHull 𝕜 (s ∪ (-s) ∪ (I : 𝕜) • s ∪ (-I : 𝕜) • s) := by
    intro x hx
    obtain ⟨r, hr, ⟨x, hx', rfl⟩⟩ := by simpa only [mem_balancedHull_iff] using hx
    have hr' := RCLike.closedBall_subset_two_smul_convexHull 𝕜 (by simpa using hr)
    simp only at hr'
    let f : 𝕜 →ₗ[𝕜] E := LinearMap.toSpanSingleton 𝕜 E x
    have hr'' : r • x ∈ f '' (2 • convexHull ℝ ({-1, 1, -I, I} : Set 𝕜)) := ⟨r, hr', rfl⟩
    rw [Set.image_nsmul, ← LinearMap.coe_toAffineMap,
      ← convexHull_rclike_eq_convexHull_real (K := 𝕜), AffineMap.image_convexHull] at hr''
    suffices 2 • (convexHull 𝕜) (⇑f.toAffineMap '' {-1, 1, -I, I}) ⊆
        2 • (convexHull 𝕜) (s ∪ -s ∪ (I : 𝕜) • s ∪ (-I : 𝕜) • s) from this hr''
    gcongr
    rintro - ⟨r, hr, rfl⟩
    obtain (rfl | rfl | rfl | rfl) : r = -1 ∨ r = 1 ∨ r = -I ∨ r = I := by simpa using hr
    · exact .inl <| .inl <| .inr <| by simpa [f] using hx'
    · exact .inl <| .inl <| .inl <| by simpa [f] using hx'
    · exact .inr ⟨x, hx', rfl⟩
    · exact .inl <| .inr <| ⟨x, hx', rfl⟩
  rw [convex_convexHull 𝕜 _ |>.nsmul_eq_smul_set _ two_ne_zero,
    ← @smul_one_smul _ _ 𝕜 _ _ _ Set.smulSet] at this
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one, neg_smul_set] at this
  suffices h_cpct : IsCompact ((2 : 𝕜) • (convexHull 𝕜) (s ∪ -s ∪ (I : 𝕜) • s ∪ -((I : 𝕜) • s))) by
    apply h_cpct.of_isClosed_subset isClosed_closedAbsConvexHull
    rw [closedAbsConvexHull_eq_closure_absConvexHull, absConvexHull_eq_convexHull_balancedHull]
    rw [h_cpct.isClosed.closure_subset_iff]
    apply convexHull_min ?_ <| (convex_convexHull ..).smul _
    grw [this, ← neg_smul_set]
  apply IsCompact.smul
  have : s ∪ -s ∪ (I : 𝕜) • s ∪ (-I : 𝕜) • s = ⋃₀ {s, -s, (I : 𝕜) • s, (-I : 𝕜) • s} := by
    simp [sUnion_insert, union_assoc]
  rw [← neg_smul_set, this]
  apply IsCompact.convexHull_biUnion (by simp)
  · grind [IsCompact.smul, IsCompact.neg]
  · grind [Convex.smul, Convex.neg]
