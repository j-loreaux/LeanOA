import LeanOA.TendstoZero.StrongDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Convex.NNReal

/-! # Krein-Smulian theorem

This file establishes the Krein-Smulian theorem. If `A : Set (WeakDual 𝕜 E)` is
convex and its intersection with arbitrrarily large closed balls is closed, then
`A` is itself closed. As a corollary if the intersection of
`A : Submodule ℝ≥0 (WeakDual 𝕜 E)` with the closed unit ball is closed, then `A` is
itself closed.

We follow the proof in Conway's "A Course in Functional Analysis", Theorem 12.1
-/

open scoped ENNReal NNReal Topology Pointwise Set.Notation tendstoZero lp ComplexOrder
open Metric Set WeakDual Filter

-- we should deprecate `convex_RCLike_iff_convex_real` eventually to be lowercase
alias ⟨Convex.of_rclike, Convex.to_rclike⟩ := convex_RCLike_iff_convex_real

section Polar

variable {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

theorem LinearMap.polar_iUnion₂ {ι} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E} :
    B.polar (⋃ i, ⋃ j, s i j) = ⋂ i, ⋂ j,  B.polar (s i j) := by
  simp

end Polar


section StrongDual

/-- If `f : StrongDual 𝕜 E` is a continuous linear functional such that the real
part of `f x` is bounded by `r` for all `x` in the unit ball, then `‖f‖ ≤ r`. -/
lemma StrongDual.norm_le_of_forall_mem_ball_re_le
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : StrongDual 𝕜 E) (r : ℝ) (hf : ∀ x ∈ ball 0 1, RCLike.re (f x) ≤ r) :
    ‖f‖ ≤ r := by
  refine f.sSup_unit_ball_eq_norm ▸ csSup_le (nonempty_ball.mpr zero_lt_one |>.image _) ?_
  rintro - ⟨x, hx, rfl⟩
  by_cases! hfx : f x = 0
  · simpa [hfx] using hf 0 (by simp)
  · simpa [hfx] using
      hf ((‖f x‖ : 𝕜) • (f x)⁻¹ • x) (by simpa [norm_smul, hfx] using hx)

end StrongDual


variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace KreinSmulian

/-- An abbreviation for the hypothesis of the Krein-Smulian theorem: the intersection of `A`
with every closed ball centered at the origin is closed. -/
abbrev KreinSmulianProperty (A : Set (WeakDual 𝕜 E)) : Prop :=
  ∀ r, IsClosed (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))

variable (A : Set (WeakDual 𝕜 E))

-- Auxiliary result contained in the proof of Lemma 12.3
/-- This is in some sense the key lemma used to prove the Krein-Smulian theorem. Suppse that the
intersection of `A : Set (WeakDual 𝕜 E)` with some closed ball of radius `t` is closed and that
for some set `F : Set E`, the intersection of `A` with a closed ball of radius `s` (`< t`) is
disjoint from the polar of `F`. Then we may adjoin a finite set `G` to `F`, with
`G ⊆ closedBall 0 s⁻¹` so that the polar of `F ∪ G` is disjoint from `A` intersected with the
larger ball of radius `t`. -/
lemma separationSeq_induction_step_aux {s t : ℝ} (hs : 0 < s) (ht : s < t)
    (hA : IsClosed (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) t)))
    (F : Set E) (hF : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) s) ∩ polar 𝕜 F = ∅) :
    ∃ G : Set E, G.Finite ∧ G ⊆ closedBall (0 : E) s⁻¹ ∧
      A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) t) ∩ polar 𝕜 F ∩ polar 𝕜 G = ∅ := by
  have h_cpct : IsCompact (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) t) ∩ polar 𝕜 F) :=
    isCompact_closedBall 𝕜 0 t |>.of_isClosed_subset hA (by simp) |>.inter_right <|
      isClosed_polar 𝕜 F
  let ι := {G : Set E // G.Finite ∧ G ⊆ closedBall (0 : E) s⁻¹}
  have : Nonempty ι := ⟨∅, by simp⟩
  let T (G : ι) : Set (WeakDual 𝕜 E) := polar 𝕜 (G : Set E)
  have hTc (G : ι) : IsClosed (T G) := isClosed_polar 𝕜 (G : Set E)
  have key : ⋂ i, T i = toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) s := by
    conv_lhs => simp [ι, iInter_subtype, T]
    rw [← NormedSpace.sInter_polar_eq_closedBall hs]
    simp [preimage_iInter, ← polar.eq_1]
  have hsT : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) t) ∩
      polar 𝕜 F ∩ ⋂ i, T i = ∅ := by
    rw [key, inter_right_comm, inter_assoc A, ← preimage_inter]
    convert hF
    exact inter_eq_self_of_subset_right <| closedBall_subset_closedBall ht.le
  have h_dir : Directed (· ⊇ ·) T := by
    intro ⟨G, hG₁, hG₂⟩ ⟨H, hH₁, hH₂⟩
    simp only [Subtype.exists, exists_and_left, exists_prop, ι, T]
    refine ⟨G ∪ H, ?sub1, ⟨hG₁.union hH₁, union_subset hG₂ hH₂⟩, ?sub2⟩
    case sub1 | sub2 => exact LinearMap.polar_antitone _ (by simp)
  simpa [ι, T, and_assoc] using h_cpct.elim_directed_family_closed T hTc hsT h_dir

/-- Suppose `A : Set (WeakDual 𝕜 E)` satisfies the `KreinSmulianProperty` and it's polar
does not intersect the unit ball. This is a sequence `F` of pairs of finite sets defined
recursively by: `F 0 := ({0}, {0})`, `(F (n + 1)).2 := (F n).2 ∪ (F (n + 1)).1` and
`(F (n + 1)).1` is the result of applying `separationSeq_induction_step_aux`
to `(F n).2`. -/
noncomputable def separationSeq (hA : KreinSmulianProperty A)
    (hA' : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) :
    (n : ℕ) → Σ' F : Set E × Set E,
      F.1.Finite ∧ F.2.Finite ∧ (F.1 : Set E) ⊆ closedBall (0 : E) (n⁻¹ : ℝ) ∧
      (A ∩ toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (n + 1)) ∩ polar 𝕜 F.2 = ∅
  | 0 => ⟨⟨{0}, {0}⟩, by simpa [polar]⟩
  | n + 1 => by
    letI ind := separationSeq_induction_step_aux A (s := n + 1) (t := n + 2) (by positivity)
      (by simp) (hA (n + 2)) (separationSeq hA hA' n).fst.2 (separationSeq hA hA' n).snd.2.2.2
    letI F₁ := ind.choose
    letI F₂ := (separationSeq hA hA' n).fst.2 ∪ F₁
    refine ⟨⟨F₁, F₂⟩, ind.choose_spec.1, (separationSeq hA hA' n).snd.2.1.union ind.choose_spec.1,
      by simpa using ind.choose_spec.2.1, ?_⟩
    have := by simpa using ind.choose_spec.2.2
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, inter_assoc] at this ⊢
    convert this using 3
    simp only [polar, ← preimage_inter, F₂, F₁]
    congr! 1
    simp only [StrongDual.polar, LinearMap.polar_union, preimage_inter]
    congr! 3
    simp [inter_assoc]

lemma separationSeq_apply_fst_snd_eq_iUnion (hA : KreinSmulianProperty A)
    (hA' : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) (n : ℕ) :
    (separationSeq A hA hA' n).fst.snd =
      ⋃ k ∈ Finset.range (n + 1), (separationSeq A hA hA' k).fst.fst := by
  induction n with
  | zero => simp [separationSeq]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm, ← ih]
    rfl

/-- Extracts `separationSeq` out into an existential statement for easier use. -/
lemma separation_aux (hA : KreinSmulianProperty A)
    (hA' : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) :
    ∃ F : ℕ → Set E, ∀ n, (F n).Finite ∧
      (F n : Set E) ⊆ closedBall (0 : E) (n⁻¹ : ℝ) ∧
      (A ∩ toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (n + 1)) ∩
        (⋂ k ∈ Finset.range (n + 1), polar 𝕜 (F k)) = ∅ := by
  use fun n ↦ (separationSeq A hA hA' n).fst.fst
  refine fun n ↦ ⟨(separationSeq A hA hA' n).snd.1, (separationSeq A hA hA' n).snd.2.2.1, ?_⟩
  convert (separationSeq A hA hA' n).snd.2.2.2 using 2
  rw [separationSeq_apply_fst_snd_eq_iUnion, polar]
  exact LinearMap.polar_iUnion₂ _ |>.symm

/-- The sequence obtained in `separation_aux` tends to zero along the cofinite filter
(on the subtype domain). -/
lemma separation_aux_tendsto
    (F : ℕ → Set E) (hF₁ : ∀ (x : ℕ), (F x).Finite)
    (hF₂ : ∀ (x : ℕ), F x ⊆ closedBall 0 (↑x)⁻¹) :
    Tendsto (fun i : ⋃ n, F n ↦ ‖(i : E)‖) cofinite (𝓝 0) := by
  rw [Metric.nhds_basis_closedBall_inv_nat_succ.tendsto_right_iff]
  rintro n -
  rw [← Subtype.val_injective.comap_cofinite_eq, Filter.eventually_comap]
  have hFn : (⋃ k ∈ (Finset.range (n + 1) : Set ℕ), F k).Finite :=
    Finset.range (n + 1) |>.finite_toSet.biUnion fun k _ ↦ (hF₁ k)
  filter_upwards [hFn.compl_mem_cofinite]
  rintro - hx ⟨x, hx'⟩ rfl
  obtain ⟨m, hxm⟩ := mem_iUnion.mp hx'
  simp only [Finset.coe_range, mem_Iio, Order.lt_add_one_iff, compl_iUnion, mem_iInter,
    mem_compl_iff] at hx
  have hmn : (n + 1 : ℝ) ≤ m := by norm_cast; grind
  have hm_pos : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hmn
  simpa using closedBall_subset_closedBall (by field_simp; assumption) <| hF₂ m hxm

-- Lemma 12.3, a separation lemma
open scoped lp Set.Notation ComplexOrder in
set_option linter.style.setOption false in
set_option maxHeartbeats 400000 in
-- because we need it
lemma separation [CompleteSpace E] (hA : KreinSmulianProperty A) (h_conv : Convex 𝕜 A)
    (hA' : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) :
    ∃ r > 0, ∃ x : E, ∀ f ∈ A, r ≤ RCLike.re (f x) := by
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := by simpa [forall_and] using separation_aux A hA hA'
  let ι := ⋃ n, F n
  let x : c₀(ι, E) := tendstoZero.mk Subtype.val <| separation_aux_tendsto F hF₁ hF₂
  let T : WeakDual 𝕜 E →ₗ[𝕜] c₀(ι, 𝕜) :=
    { toFun φ := tendstoZero.mapCLM (fun _ ↦ toStrongDual φ) (norm_nonneg _) (fun _ ↦ le_rfl) x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hTA : Disjoint (ball 0 1) (T '' A) := by
    rw [← compl_compl (ball _ _), disjoint_compl_left_iff_subset]
    rintro - ⟨φ, hφ, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (‖toStrongDual φ‖ - 1)
    rw [sub_le_iff_le_add] at hn
    specialize hF₃ n
    have : φ ∉ ⋂ k ∈ Finset.range (n + 1), polar 𝕜 (F k) :=
      fun hφ ↦ (hF₃ ▸ notMem_empty φ) <| by clear hF₃; aesop
    simp only [Finset.mem_range, Order.lt_add_one_iff, mem_iInter, not_forall, exists_prop] at this
    obtain ⟨k, hkF, hφF⟩ := this
    simp only [polar, mem_preimage, coe_toStrongDual, StrongDual.mem_polar_iff, not_forall,
      exists_prop, not_le] at hφF
    obtain ⟨i, hi, hφi⟩ := hφF
    rw [mem_compl_iff, Metric.mem_ball, dist_eq_norm, not_lt, sub_zero]
    apply hφi.le.trans
    exact lp.norm_apply_le_norm (by simp) (T φ : ℓ^∞(ι, 𝕜)) ⟨i, mem_iUnion.mpr ⟨k, hi⟩⟩
  replace hA := h_conv.linear_image T |>.of_rclike
  obtain ⟨f, u, hfu1, hfuA⟩ :=
    RCLike.geometric_hahn_banach_open (𝕜 := 𝕜) (convex_ball 0 1) isOpen_ball hA hTA
  obtain (rfl | hA_nonempty) := A.eq_empty_or_nonempty
  · exact ⟨1, zero_lt_one, 0, by simp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using hfu1 0 (by simp) |>.trans_le <| hfuA _ ⟨_, hA_nonempty.some_mem, rfl⟩
  classical
  have : ∀ b ∈ T '' A, ‖f‖ ≤ RCLike.re (f b) := by
    have := f.norm_le_of_forall_mem_ball_re_le u (fun b hb ↦ (hfu1 b hb).le)
    exact fun b hb ↦ this.trans (hfuA b hb)
  refine ⟨‖f‖, by simpa using hf, ?_⟩
  let x' := tendstoZero.lpOneToStrongDualₗᵢ ι 𝕜 |>.symm f
  use lp.dualPairing 1 ∞ _ (K := 1)
    (fun _ ↦ ContinuousLinearMap.opNorm_lsmul_le (𝕜 := 𝕜) (R := 𝕜) (E := E)) x' x
  intro φ hφ
  convert this _ ⟨φ, hφ, rfl⟩
  simp only [lp.dualPairing_apply]
  rw [← toStrongDual_apply, (toStrongDual φ).map_tsum]
  · simp only [coe_toStrongDual, ContinuousLinearMap.lsmul_apply, map_smul, smul_eq_mul]
    conv_rhs =>
      rw [← (tendstoZero.lpOneToStrongDualₗᵢ ι 𝕜).apply_symm_apply f]
      rw [tendstoZero.lpOneToStrongDualₗᵢ_apply_apply]
    simp [T, lp.scalarDualPairing, lp.dualPairing_apply, x', mul_comm]
    rfl
  · exact (lp.memℓp x').holder 1 (lp.memℓp (x : ℓ^∞(ι, E)))
      (fun _ ↦ ContinuousLinearMap.lsmul 𝕜 𝕜)
      (fun _ ↦ ContinuousLinearMap.opNorm_lsmul_le) |>.summable_of_one

lemma KreinSmulianProperty.isClosed_inter_closedBall
    (hA : KreinSmulianProperty A) (x : WeakDual 𝕜 E) (r : ℝ) :
    IsClosed (A ∩ toStrongDual ⁻¹' closedBall (toStrongDual x) r) := by
  have := Metric.closedBall_subset_closedBall' (ε₂ := r + dist (toStrongDual x) 0) le_rfl
  rw [← inter_eq_right.mpr this, preimage_inter, ← inter_assoc]
  exact hA _ |>.inter <| isClosed_closedBall ..

lemma KreinSmulianProperty.translate (hA : KreinSmulianProperty A) (x : WeakDual 𝕜 E) :
    KreinSmulianProperty (x +ᵥ A) := by
  intro r
  convert hA.isClosed_inter_closedBall _ (-x) r |>.vadd x using 1
  ext φ
  simp [vadd_set_inter, mem_vadd_set]
  aesop (add simp [dist_eq_norm, add_comm])

lemma KreinSmulianProperty.dilate (hA : KreinSmulianProperty A) (c : 𝕜) :
    KreinSmulianProperty (c • A) := by
  by_cases hc : c = 0
  · obtain (rfl | hA') := A.eq_empty_or_nonempty
    · simpa
    · simpa [KreinSmulianProperty, hc, zero_smul_set, hA', ← Set.singleton_zero]
        using fun r ↦ isClosed_singleton.inter <| isClosed_closedBall 0 r
  · intro r
    have := hA (r / ‖c‖) |>.smul₀ c
    simp only [smul_set_inter₀ hc, ← IsUnit.mk0 _ hc |>.preimage_smul_set] at this
    simpa only [ne_eq, hc, not_false_eq_true, smul_closedBall', smul_zero, norm_eq_zero,
      mul_div_cancel₀]

lemma KreinSmulianProperty.isClosed_toStrongDual (hA : KreinSmulianProperty A) :
    IsClosed (toStrongDual '' A) := by
  simp_rw [isClosed_iff_frequently, Filter.frequently_iff_seq_forall]
  rintro φ₀ ⟨φ, hφ, hφ_mem⟩
  obtain ⟨r, hr⟩ := Metric.isBounded_range_of_tendsto φ hφ |>.subset_closedBall φ₀
  replace hφ := by simpa only [Function.comp_def] using
    NormedSpace.Dual.toWeakDual_continuous.tendsto φ₀ |>.comp hφ
  replace hφ_mem (n : ℕ) : (φ n).toWeakDual ∈ A ∩ toStrongDual ⁻¹' closedBall φ₀ r := by
    rw [toStrongDual.image_eq_preimage_symm] at hφ_mem
    exact ⟨hφ_mem n, by simpa using hr ⟨n, rfl⟩⟩
  replace hA := hA.isClosed_inter_closedBall _ (φ₀.toWeakDual) r
  exact ⟨_, hA.mem_of_tendsto hφ (.of_forall hφ_mem) |>.1, by simp⟩

lemma KreinSmulianProperty.of_frequently
    (hA : ∃ᶠ r in atTop, IsClosed (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))) :
    KreinSmulianProperty A := by
  intro r
  obtain ⟨s, hrs ,hs⟩ := hA.forall_exists_of_atTop r
  convert inter_assoc .. ▸ hs.inter (isClosed_closedBall 0 r) using 2
  exact Eq.symm <| inter_eq_right.mpr <| preimage_mono <| closedBall_subset_closedBall hrs

attribute [fun_prop] WeakDual.eval_continuous

end KreinSmulian

open KreinSmulian

/-- The **Krein-Smulian theorem**. If `A : Set (WeakDual 𝕜 E)` is convex and its intersection with
arbitrarily large closed balls is closed, then `A` is itself closed (in the weak⋆ topology). -/
theorem krein_smulian [CompleteSpace E] (A : Set (WeakDual 𝕜 E))
    (hA : ∃ᶠ r in atTop, IsClosed (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r)))
    (hA_conv : Convex 𝕜 A) : IsClosed A := by
  replace hA : KreinSmulianProperty A := .of_frequently _ hA
  apply isClosed_of_closure_subset fun φ₀ hφ₀ ↦ ?_
  contrapose hφ₀
  have hφ₀' : toStrongDual φ₀ ∉ toStrongDual '' A := by rintro ⟨φ, hφ, rfl⟩; exact hφ₀ hφ
  obtain ⟨r, hr, hrA⟩ := nhds_basis_closedBall.mem_iff.mp <|
    hA.isClosed_toStrongDual.compl_mem_nhds hφ₀'
  rw [← disjoint_compl_right_iff_subset, compl_compl, Set.disjoint_image_right] at hrA
  replace hA := hA.translate _ (-φ₀) |>.dilate _ (r⁻¹ : 𝕜)
  replace hA_conv := hA_conv.vadd (-φ₀) |>.smul (r⁻¹ : 𝕜)
  have ⟨s, hs, x, hx⟩ := separation _ hA hA_conv <| by
    rw [← disjoint_iff_inter_eq_empty, disjoint_comm]
    rw [← compl_compl (toStrongDual ⁻¹' _), disjoint_compl_left_iff_subset] at hrA ⊢
    rintro z ⟨y, ⟨x, hxA, rfl⟩, rfl⟩
    simpa [add_comm, ← sub_eq_add_neg, norm_smul, one_lt_inv_mul₀,
      abs_of_pos, hr, dist_eq_norm] using hrA hxA
  simp only [mem_smul_set, mem_vadd_set, vadd_eq_add, exists_exists_and_eq_and, smul_add, smul_neg,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hx
  intro hφ_mem
  have := closure_minimal hx (t := {a | s ≤ RCLike.re ((-((r : 𝕜)⁻¹ • φ₀) + (r : 𝕜)⁻¹ • a) x)}) (by
    apply isClosed_le (by fun_prop)
    change Continuous
      fun b : WeakDual 𝕜 E ↦ RCLike.re (-((r : 𝕜)⁻¹ • φ₀ x)  + (r : 𝕜)⁻¹ • b x)
    fun_prop)
  replace this := this hφ_mem
  simp only [mem_setOf_eq, neg_add_cancel] at this
  change s ≤ RCLike.re 0 at this -- grrrr...
  simp only [map_zero] at this
  exact lt_irrefl _ <| hs.trans_le this

/-- The **Krein-Smulian theorem**. If `A : Submodule 𝕜 (WeakDual 𝕜 E)` and if
the intersection of `A` with the closed unit ball is closed, then `A` is itself
closed (in the weak⋆ topology). -/
lemma krein_smulian_of_submodule [CompleteSpace E] (A : Submodule ℝ≥0 (WeakDual 𝕜 E))
    (hA : IsClosed ((A : Set (WeakDual 𝕜 E)) ∩ (toStrongDual ⁻¹' closedBall 0 1))) :
    IsClosed (A : Set (WeakDual 𝕜 E)) := by
  refine krein_smulian (A : Set (WeakDual 𝕜 E)) (Filter.Eventually.frequently ?_)
    (.to_rclike <| NNReal.convex_iff.mp A.convex)
  filter_upwards [Filter.Ioi_mem_atTop 0] with r (hr : 0 < r)
  lift r to ℝ≥0 using hr.le
  lift r to ℝ≥0ˣ using IsUnit.mk0 _ (mod_cast hr.ne')
  have := hA.smul r
  rw [smul_set_inter] at this
  convert this using 2 <;> ext
  · simp [mem_smul_set_iff_inv_smul_mem]
  · simp [mem_smul_set_iff_inv_smul_mem₀, Units.smul_def,
      NNReal.smul_def, norm_smul, inv_mul_le_one₀ hr]
