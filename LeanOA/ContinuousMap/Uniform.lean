import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.CompactConvergence

open Filter Topology
open scoped UniformConvergence NNReal

section ContinuousMap

variable {X α β : Type*} [TopologicalSpace X] [TopologicalSpace α] [UniformSpace β]

open UniformOnFun in
/-- `f : X → C(α, β)` is continuous if any only if it is continuous when reinterpreted as a
map `f : X → α →ᵤ[{K | IsCompact K}] β`. -/
theorem ContinuousMap.continuous_iff_continuous_uniformOnFun (f : X → C(α, β)) :
    Continuous f ↔ Continuous (fun x ↦ ofFun {K | IsCompact K} (f x)) :=
  isUniformEmbedding_toUniformOnFunIsCompact.isInducing.continuous_iff

open UniformFun in
/-- When `α` is compact, `f : X → C(α, β)` is continuous if any only if it is continuous when
reinterpreted as a map `f : X → α →ᵤ β`. -/
theorem ContinuousMap.continuous_iff_continuous_uniformFun (f : X → C(α, β)) [CompactSpace α] :
    Continuous f ↔ Continuous (fun x ↦ ofFun (f x)) := by
  rw [continuous_iff_continuous_uniformOnFun]
  exact UniformOnFun.uniformEquivUniformFun β _ isCompact_univ
    |>.isUniformInducing.isInducing.continuous_iff

/-- Given functions `F i, f` which are continuous on a compact set `s`, `F` tends to `f`
uniformly on `s` if and only if the restrictions (as elements of `C(s, β)`) converge. -/
theorem ContinuousOn.tendsto_restrict_iff_tendstoUniformlyOn {s : Set α} [CompactSpace s]
    {f : α → β} (hf : ContinuousOn f s) {ι : Type*} {p : Filter ι}
    {F : ι → α → β} (hF : ∀ i, ContinuousOn (F i) s) :
    Tendsto (fun i ↦ ⟨_, (hF i).restrict⟩ : ι → C(s, β)) p (𝓝 ⟨_, hf.restrict⟩) ↔
      TendstoUniformlyOn F f p s := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  congr!

open UniformOnFun in
/-- A family `f : X → α → β`, each of which is continuous on a compact set `s : Set α` is
continuous in the topology `X → α →ᵤ[{s}] β` if and only if the family of continuous restrictions
`X → C(s, β)` is continuous. -/
theorem ContinuousOn.continuous_restrict_iff_continuous_uniformOnFun
    {f : X → α → β} {s : Set α} (hf : ∀ x, ContinuousOn (f x) s) [CompactSpace s] :
    Continuous (fun x ↦ ⟨_, (hf x).restrict⟩ : X → C(s, β)) ↔
      Continuous (fun x ↦ ofFun {s} (f x)) := by
  rw [ContinuousMap.continuous_iff_continuous_uniformFun, UniformOnFun.continuous_rng_iff]
  simp [Function.comp_def]

end ContinuousMap

section TendstoUniformlyBasis

namespace Filter.HasBasis

variable {X ι ιX ια ιβ α β : Type*} {𝔖 : Set (Set α)} [UniformSpace β]

open UniformFun

/-- An anologue of `Filter.Tendsto.tendsto_right_iff` for `TendstoUniformlyOnFilter`. -/
lemma uniformity_tendstoUniformlyOnFilter_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∀ᶠ n in l ×ˢ l', (f n.2, F n.1 n.2) ∈ sβ i) := by
  rw [TendstoUniformlyOnFilter, hβ.forall_iff]
  exact fun _ _ _ h ↦ h.mp <| .of_forall <| by aesop

/-- An anologue of `Filter.Tendsto.tendsto_right_iff` for `TendstoUniformlyOn`. -/
lemma tendstoUniformlyOnFilter_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pX : ιX → Prop} {sX : ιX → Set X}
    {pα : ια → Prop} {sα : ια → Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hl : l.HasBasis pX sX) (hl' : l'.HasBasis pα sα)
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∃ j k, (pX j ∧ pα k) ∧ ∀ x a, x ∈ sX j → a ∈ sα k → (f a, F x a) ∈ sβ i) := by
  simp [hβ.uniformity_tendstoUniformlyOnFilter_iff, (hl.prod hl').eventually_iff]

/-- An anologue of `Filter.Tendsto.tendsto_right_iff` for `TendstoUniformly`. -/
lemma uniformity_tendstoUniformlyOn_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x ∈ s, (f x, F n x) ∈ sβ i) := by
  rw [TendstoUniformlyOn, hβ.forall_iff]
  exact fun _ _ _ h ↦ h.mp <| .of_forall <| by aesop

/-- An anologue of `Filter.Tendsto.tendsto_iff` for `TendstoUniformlyOnFilter`. -/
lemma tendstoUniformlyOn_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pX : ιX → Prop} {sX : ιX → Set X} {pβ : ιβ → Prop}
    {sβ : ιβ → Set (β × β)} (hl : l.HasBasis pX sX) (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a ∈ s, (f a, F x a) ∈ sβ i) := by
  simp [hβ.uniformity_tendstoUniformlyOn_iff, hl.eventually_iff]

/-- An anologue of `Filter.Tendsto.tendsto_iff` for `TendstoUniformlyOn`. -/
lemma uniformity_tendstoUniformly_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x, (f x, F n x) ∈ sβ i) := by
  rw [TendstoUniformly, hβ.forall_iff]
  exact fun _ _ _ h ↦ h.mp <| .of_forall <| by aesop

/-- An anologue of `Filter.Tendsto.tendsto_iff` for `TendstoUniformly`. -/
lemma tendstoUniformly_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {pX : ιX → Prop} {sX : ιX → Set X} (hl : l.HasBasis pX sX)
    {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)} (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a, (f a, F x a) ∈ sβ i) := by
  simp only [hβ.uniformity_tendstoUniformly_iff, hl.eventually_iff]

end Filter.HasBasis

end TendstoUniformlyBasis

section Lipschitz

variable {X α β : Type*} {𝔖 : Set (Set α)} [PseudoMetricSpace X] [PseudoMetricSpace β]

/-- If `f : X → α →ᵤ[𝔖] β` is Lipschitz for each fixed `a ∈ s ∈ 𝔖`, with Lipschitz
constant depending on `s`, then `f` is continuous. -/
lemma UniformOnFun.continuous_of_lipschitzWith {f : X → α →ᵤ[𝔖] β}
    (C : Set α → ℝ≥0) (hf : ∀ s ∈ 𝔖, ∀ a ∈ s, LipschitzWith (C s) (fun x ↦ toFun _ (f x) a)) :
    Continuous f := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Metric.nhds_basis_closedBall.tendstoUniformlyOn_iff Metric.uniformity_basis_dist_le]
  refine fun x₀ s hs ε hε ↦ ⟨ε / (C s + 1), by positivity, fun x hx a ha ↦ ?_⟩
  simp only [Metric.mem_closedBall, dist_comm x, Function.comp_apply, Set.mem_setOf_eq] at hx ⊢
  calc
    _ ≤ C s * dist x₀ x := (hf s hs a ha).dist_le_mul _ _
    _ ≤ C s * (ε / (C s + 1)) := by gcongr
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀' (by positivity)]
      gcongr
      simp

/-- If `f : X → α →ᵤ β` is Lipschitz for each fixed `a ∈ s ∈ 𝔖`, with Lipschitz
constant depending on `s`, then `f` is continuous. -/
lemma UniformFun.continuous_of_lipschitzWith {f : X → α →ᵤ β} (C : ℝ≥0)
    (hf : ∀ a, LipschitzWith C (fun x ↦ toFun (f x) a)) :
    Continuous f := by
  let e := UniformOnFun.uniformEquivUniformFun (α := α) (𝔖 := {Set.univ}) β (by simp)
  rw [e.symm.isUniformInducing.isInducing.continuous_iff]
  apply UniformOnFun.continuous_of_lipschitzWith (fun _ ↦ C)
  rintro - - a -
  exact hf a

end Lipschitz
