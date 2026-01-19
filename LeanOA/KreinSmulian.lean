import Mathlib
import LeanOA.TendstoZero.StrongDual


-- We follow the proof in Conway's "A Course in Functional Analysis", Theorem 12.1

-- Lemma 12.2

open scoped ENNReal NNReal Topology
open Metric Set WeakDual

-- we should deprecate `convex_RCLike_iff_convex_real` eventually to be lowercase
alias ⟨Convex.of_rclike, Convex.to_rclike⟩ := convex_RCLike_iff_convex_real

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
does not intersect the unit ball. This is a sequence `F` of pairs of finite sets defined
recursively by: `F 0 := ({0}, {0})`, `(F (n + 1)).2 := (F n).2 ∪ (F (n + 1)).1` and
`(F (n + 1)).1` is the result of applying `krein_smulian_separation_induction_step_aux`
to `(F n).2`. -/
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
@[simp]
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

def _root_.lp.norm_mono {ι : Type*} {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedAddCommGroup (F i)] {p : ℝ≥0∞} (hp : p ≠ 0)
    {x : lp E p} {y : lp F p} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖x‖ ≤ ‖y‖ := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp at hp
  · exact lp.norm_le_of_forall_le (by positivity)
      fun i ↦(h i).trans <|lp.norm_apply_le_norm hp y i
  · exact lp.norm_le_of_forall_sum_le hp (lp.norm_nonneg' _) fun s ↦ calc
      ∑ i ∈ s, ‖x i‖ ^ p.toReal
      _ ≤ ∑ i ∈ s, ‖y i‖ ^ p.toReal := by gcongr with i _; exact h i
      _ ≤ ‖y‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hp y s

/-- A uniformly bounded family of continuous linear maps, as a continuous linear map
on the `lp` space. -/
@[simps!]
def _root_.lp.mapCLM {ι : Type*} {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    lp E p →L[𝕜] lp F p :=
  haveI key (i : ι) (x : E i) : ‖T i x‖ ≤ ‖(K : 𝕜) • x‖ := by
    simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hK]
      using (T i).le_of_opNorm_le (hTK i) _
  LinearMap.mkContinuous
    { toFun x := ⟨fun i ↦ T i (x i), lp.memℓp x |>.const_smul (K : 𝕜) |>.mono fun _ ↦ key ..⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    K
    fun x ↦ by
      trans ‖(K : 𝕜) • x‖
      · have : p ≠ 0 := by have := Fact.out (p := 1 ≤ p); exact ne_of_gt (zero_lt_one.trans_le this)
        exact lp.norm_mono this fun i ↦ by simpa using key i (x i)
      · simp [norm_smul, abs_of_nonneg hK]

lemma _root_.lp.norm_mapCLM_le {ι : Type*} {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    ‖lp.mapCLM p T hK hTK‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ hK _

variable (𝕜) in
open tendstoZero in
/-- The linear isometry equivalence between `c₀ E` and itself, viewed as a
submodule of `lp E ∞` (as opposed to only an `AddSubgroup`). -/
noncomputable def _root_.tendstoZero.toSubmoduleLinearIsometryEquiv {ι : Type*} (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    toSubmodule 𝕜 E ≃ₗᵢ[𝕜] c₀ E :=
  LinearIsometryEquiv.refl ..

open tendstoZero in
lemma _root_.lp.mapCLM_mem_tendstoZero {ι : Type*} {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)] (T : ∀ i, E i →L[𝕜] F i)
    {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) (x : lp E ∞) (hx : x ∈ c₀ E) :
    lp.mapCLM ∞ T hK hTK x ∈ c₀ F :=
  tendsto_const_nhds.squeeze (mul_zero K ▸ hx.const_mul K) (fun _ ↦ by simp)
    fun i ↦ (T i).le_of_opNorm_le (hTK i) _

open tendstoZero in
@[simps!]
noncomputable def _root_.tendstoZero.mapCLM {ι : Type*} {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)]
    (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    c₀ E →L[𝕜] c₀ F :=
  letI e₁ := tendstoZero.subtypeₗᵢ 𝕜 E |>.toContinuousLinearMap
  letI e₂ := lp.mapCLM ∞ T hK hTK
  letI e₃ := toSubmoduleLinearIsometryEquiv 𝕜 F
    |>.symm.toContinuousLinearEquiv.toContinuousLinearMap
  e₃ ∘L ((e₂ ∘L e₁).codRestrict (tendstoZero.toSubmodule 𝕜 F)
    fun x ↦ lp.mapCLM_mem_tendstoZero T hK hTK x.1 x.2)

open Filter tendstoZero Set.Notation in
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

open tendstoZero
lemma _root_.tendstsoZero.coe_smul {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (a : 𝕜) (x : c₀ E) :
    ↑(a • x) = (a • x : lp E ∞) := by
  simp only [tendstoZero.coe_smul]

lemma _root_.StrongDual.norm_le_of_forall_mem_ball_re_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : StrongDual 𝕜 E) (r : ℝ) (hf : ∀ x ∈ ball 0 1, RCLike.re (f x) ≤ r) :
    ‖f‖ ≤ r := by
  refine f.sSup_unit_ball_eq_norm ▸ csSup_le (nonempty_ball.mpr zero_lt_one |>.image _) ?_
  rintro - ⟨x, hx, rfl⟩
  by_cases! hfx : f x = 0
  · simpa [hfx] using hf 0 (by simp)
  · simpa [hfx] using
      hf ((‖f x‖ : 𝕜) • (f x)⁻¹ • x) (by simpa [norm_smul, hfx] using hx)

lemma _root_.Memℓp.summable_of_one {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {x : ι → E}
    (hx : Memℓp x 1) : Summable x :=
  .of_norm <| by simpa using hx.summable

open tendstoZero
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
  let x : c₀(ι, E) := mk Subtype.val <| separation_aux_tendsto F hF₁ hF₂
  let T : WeakDual 𝕜 E →ₗ[𝕜] c₀(ι, 𝕜) :=
    { toFun φ := mapCLM (fun _ ↦ toStrongDual φ) (norm_nonneg _) (fun _ ↦ le_rfl) x
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
  have : IsScalarTower ℝ 𝕜 c₀(ι, 𝕜) := by
    refine ⟨fun x y z ↦ ?_⟩
    ext
    rw [tendstoZero.coe_smul] -- not sure why this is necessary, probably abusing defeq
    simp
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

open Pointwise in
lemma KreinSmulianProperty.translate (hA : KreinSmulianProperty A) (x : WeakDual 𝕜 E) :
    KreinSmulianProperty (x +ᵥ A) := by
  intro r
  convert hA.isClosed_inter_closedBall _ (-x) r |>.vadd x using 1
  ext φ
  simp [vadd_set_inter, mem_vadd_set]
  aesop (add simp [dist_eq_norm, add_comm])

open Pointwise in
lemma KreinSmulianProperty.dilate (hA : KreinSmulianProperty A) (c : 𝕜) :
    KreinSmulianProperty (c • A) := by
  by_cases hc : c = 0
  · obtain (rfl | hA') := A.eq_empty_or_nonempty
    · simpa
    · simp [KreinSmulianProperty, hc, zero_smul_set, hA', ← Set.singleton_zero]
      sorry
  · intro r
    have := hA (r / ‖c‖) |>.smul₀ c
    simp only [smul_set_inter₀ hc, ← IsUnit.mk0 _ hc |>.preimage_smul_set] at this
    simpa only [ne_eq, hc, not_false_eq_true, smul_closedBall', smul_zero, norm_eq_zero,
      mul_div_cancel₀]


lemma KreinSmulianProperty.isClosed_toStrongDual (hA : KreinSmulianProperty A) (r : ℝ) :
    IsClosed (toStrongDual '' A) := by

  sorry

lemma _root_.krein_smulian (hA : KreinSmulianProperty A) : IsClosed A := by
  sorry

end KreinSmulian
