import Mathlib
import LeanOA.TendstoZero.StrongDual


-- We follow the proof in Conway's "A Course in Functional Analysis", Theorem 12.1

-- Lemma 12.2
#check NormedSpace.sInter_polar_eq_closedBall
#check WeakDual.isClosed_polar
#check IsCompact.elim_directed_family_closed

open scoped ENNReal NNReal Topology
open Metric Set WeakDual

section Polar

variable {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

@[simp]
theorem LinearMap.polar_iUnion₂ {ι} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E} :
    B.polar (⋃ i, ⋃ j, s i j) = ⋂ i, ⋂ j,  B.polar (s i j) :=
  B.polar_gc.l_iSup₂

end Polar

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace KreinSmulian

public abbrev KreinSmulianProperty (A : Set (WeakDual 𝕜 E)) : Prop :=
  ∀ r, IsClosed (A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))

variable (A : Set (WeakDual 𝕜 E))

open scoped Pointwise in
-- Auxiliary result contained in the proof of Lemma 12.3
lemma separation_induction_step_aux {s t : ℝ} (hs : 0 < s) (ht : s < t)
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
does not intersect the unit ball. This is an sequence of pairs of finite sets constructed
inductively by applying `krein_smulian_separation_induction_step_aux`. The first set in
that pair is obtained by applying the theorem to the second set in the previous pair.
The second set is the union of the two previous sets. So, the second set is the sequence
of unions of the previous first sets. -/
noncomputable def separationSeq (hA : KreinSmulianProperty A)
    (hA' : A ∩ (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) :
    (n : ℕ) → Σ' F : Set E × Set E,
      F.1.Finite ∧ F.2.Finite ∧ (F.1 : Set E) ⊆ closedBall (0 : E) (n⁻¹ : ℝ) ∧
      (A ∩ toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) (n + 1)) ∩ polar 𝕜 F.2 = ∅
  | 0 => ⟨⟨{0}, {0}⟩, by simpa [polar]⟩
  | n + 1 => by
    letI ind := separation_induction_step_aux A (s := n + 1) (t := n + 2) (by positivity)
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

open scoped Pointwise in
-- Auxiliary result contained in the proof of Lemma 12.3
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

open Filter tendstoZero in
/-- Constructor for a term of `c₀ E` which doesn't force the user to pass through `lp E ∞`. -/
def _root_.tendstoZero.mk {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) :
    c₀ E :=
  ⟨⟨f, memℓp_infty h.bddAbove_range_of_cofinite⟩, h⟩

open Filter tendstoZero in
lemma _root_.tendstoZero.coe_mk {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : (i : ι) → E i) (h : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)) :
    ⇑(mk f h : lp E ∞) = f :=
  rfl

-- this was unnecessary, but maybe we should keep it
open Uniformity in
theorem _root_.Metric.uniformity_basis_dist_le_inv_nat_succ {α : Type*} [PseudoMetricSpace α] :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩

-- this was unnecessary, but maybe we should keep it
theorem _root_.Metric.nhds_basis_closedBall_inv_nat_succ {α : Type*} [PseudoMetricSpace α] {x : α} :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ

open scoped tendstoZero lp Set.Notation ComplexOrder in
-- Lemma 12.3, a separation lemma
lemma separation (hA : KreinSmulianProperty A) (h_conv : Convex 𝕜 A)
    (hA' : A ∩ (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) = ∅) :
    ∃ x : E, ∀ f ∈ A, RCLike.re (f x) ≥ 1 := by
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := by simpa [forall_and] using separation_aux A hA hA'
  let S := ⋃ n, F n
  have hS : S.Countable := countable_iUnion fun n ↦ (hF₁ n).countable
  let T : WeakDual 𝕜 E → c₀(S, 𝕜) := fun φ ↦ tendstoZero.mk (φ ·) <| by
    sorry
    --rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
    --intro ε hε
    --obtain (rfl | hφ) := eq_or_ne φ 0
    --· exact .of_forall fun _ ↦ by simpa [Pi.zero_apply, WeakDual, WeakBilin] using hε.le
    --rw [ne_eq, ← map_eq_zero_iff _ WeakDual.toStrongDual.injective, ← ne_eq, ← norm_pos_iff] at hφ
    --obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε hφ)
    --have hFn : (⋃ k ∈ (Finset.range (n + 1) : Set ℕ), F k).Finite :=
      --Finset.range (n + 1) |>.finite_toSet.biUnion fun k _ ↦ (hF₁ k)
    --have : S ↓∩ (⋃ k ∈ ↑(Finset.range (n + 1)), F k) |>.Finite :=
      --hFn.preimage Subtype.val_injective.injOn
    --filter_upwards [this.compl_mem_cofinite] with s hs
    --simp at hs
    --obtain ⟨k, hk⟩ := by simpa [-Subtype.coe_prop, S, mem_iUnion] using s.2
    --have hkn : (k : ℝ) ≥ n + 1 := by norm_cast; grind
    --have hk_pos : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hkn
    --have := by simpa using
      --closedBall_subset_closedBall (ε₂ := 1 / (n + 1)) (by field_simp; assumption) <| hF₂ k hk
    --simp only [mem_closedBall, dist_zero_right, norm_norm, ge_iff_le]
    --calc ‖φ s‖
      --_ = ‖toStrongDual φ s‖ := rfl
      --_ ≤ ‖toStrongDual φ‖ * ‖(s : E)‖ := (toStrongDual φ).le_opNorm ..
      --_ ≤ ‖toStrongDual φ‖ * (ε / ‖toStrongDual φ‖) := by
        --gcongr
        --exact this.trans <| by simpa using hn.le
      --_ = ε := by field
  let Tₗ : WeakDual 𝕜 E →ₗ[𝕜] c₀(S, 𝕜) :=
    { toFun := T
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hT (φ : WeakDual 𝕜 E) (hx : φ ∈ A) : 1 < ‖T φ‖ := by sorry
  replace hA := h_conv.linear_image Tₗ
  have hTA : Disjoint (ball 0 1) (Tₗ '' A) := by sorry
  --need to convert to convex over `ℝ` first.
  --obtain ⟨f, u, hfu1, hfuA⟩ := RCLike.geometric_hahn_banach_open (convex_ball 0 1) isOpen_ball hA hTA
  sorry

lemma _root_.krein_smulian (hA : KreinSmulianProperty A) : IsClosed A := by
  sorry

end KreinSmulian
