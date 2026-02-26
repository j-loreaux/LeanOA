import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace

/-! # Properties of the uniformity and topology of `σ(M, P)`

This file contains some nice characterizations of the uniformity and the topology of `σ(M, P)`
in terms of positive linear functionals.

In particular, on *bounded sets*, the uniformity of `σ(M, P)` is the same as the uniformity of
on the weak topology of `M` induced by the pairing with the type, herein denoted by the private
declaration `Ultraweak.E`, of linear combinations of positive ultraweakly continuous linear
functionals. The private declaration `Ultraweak.WeakE` denotes `M` equipped with the weak topology
induced by `E`.

Crucially, `WeakE` is Hausdorff, and weaker that `σ(M, P)` which is compact on preimages (under
`ofUltraweak`) of closed and bounded sets. Therefore, the identity map from `σ(M, P)` to `WeakE` is
a uniform equivalence on bounded sets.

Consequently, a filter `l` in `σ(M, P)`, disjoint from the cobounded filter, is cauchy if and only
if `map φ l` is cauchy for every positive ultraweakly continuous linear functional `φ`. Similarly,
a function `f` defined on `σ(M, P)` whose range is eventually bounded tends to `𝓝 x` if and only
if `map φ f` tends to `𝓝 (φ x)` for every positive ultraweakly continuous linear functional `φ`.

## Main statements

-/

-- these attributes are added in #35261
attribute [push] Filter.not_neBot
attribute [push ←] Filter.neBot_iff

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

namespace Ultraweak

open scoped Topology ComplexOrder
open Filter Set Bornology

variable (M P)

/-- Linear combinations of ultraweakly continuous positive linear functionals. -/
private noncomputable def E : Submodule ℂ (StrongDual ℂ σ(M, P)) :=
  Submodule.span ℂ (Set.range PositiveContinuousLinearMap.toContinuousLinearMap)

/-- The natural bilinear induced by the pairing of `M` with `E M P`. -/
@[simps!]
private noncomputable def fromEₗ : M →ₗ[ℂ] E M P →ₗ[ℂ] ℂ :=
  letI e : E M P →ₗ[ℂ] σ(M, P) →ₗ[ℂ] ℂ :=
    (ContinuousLinearMap.coeLM ℂ).compRight ℂ (E M P).subtype
  (linearEquiv ℂ M P).arrowCongr (.refl ℂ _) e.flip

/-- `E` separates points of `M` because positive continuous linear maps
do as well. -/
private lemma fromEₗ_injective : Function.Injective (fromEₗ M P) := by
  intro x y h
  rw [← toUltraweak_inj (𝕜 := ℂ) (P := P)]
  apply ext_positiveCLM fun φ ↦ ?_
  congrm($h ⟨φ.toContinuousLinearMap, Submodule.subset_span <| by simp⟩)

/-- The weak topology on `M` induced by pairing with linear combinations of
positive continuous linear maps. -/
private abbrev WeakE := WeakBilin (fromEₗ M P)

private instance : T2Space (WeakE M P) :=
  WeakBilin.isEmbedding (fromEₗ_injective M P) |>.t2Space

-- we're missing `WeakBilin` API
private noncomputable def weakEEquiv : WeakE M P ≃ₗ[ℂ] M := .refl ℂ _

omit [StarOrderedRing M] [CompleteSpace P] in
/-- A filter is cauchy relative to the `WeakE M P` topology if and only if
mapping it through `φ` is cauchy for every `φ : σ(M, P) →P[ℂ] ℂ`. -/
private lemma cauchy_weakE_iff_forall_posCLM {l : Filter (WeakE M P)} :
    Cauchy l ↔ ∀ φ : σ(M, P) →P[ℂ] ℂ,
      Cauchy (Filter.map (fun m ↦ φ (toUltraweak ℂ P (weakEEquiv M P m))) l) := by
  rw [WeakBilin.cauchy_iff (fromEₗ M P)]
  refine ⟨fun h φ ↦ h ⟨φ.toContinuousLinearMap, Submodule.subset_span <| by simp⟩,
    fun h ⟨φ, hφ⟩ ↦ ?_⟩
  simp only [fromEₗ_apply_apply]
  have hl : l.NeBot := (h 0).1.of_map
  induction hφ using Submodule.span_induction with
  | mem φ hφ => obtain ⟨φ, hφ, rfl⟩ := hφ; exact h φ
  | zero => exact h 0
  | add φ ψ hφ hψ ihφ ihψ =>
    simpa using (ihφ.prod ihψ).mono (tendsto_map.prodMk tendsto_map) |>.map uniformContinuous_add
  | smul a φ hφ ihφ => simpa using ihφ.map <| uniformContinuous_const_smul a

private lemma tendsto_weakE_iff_forall_posCLM {α : Type*} [TopologicalSpace α]
    {l : Filter α} (x : WeakE M P) {f : α → WeakE M P} :
    Tendsto f l (𝓝 x) ↔ ∀ φ : σ(M, P) →P[ℂ] ℂ,
      Tendsto (fun m ↦ φ (toUltraweak ℂ P (weakEEquiv M P (f m)))) l
        (𝓝 (φ (toUltraweak ℂ P (weakEEquiv M P x)))) := by
  rw [WeakBilin.tendsto_iff_forall_eval_tendsto (fromEₗ M P) (fromEₗ_injective M P)]
  refine ⟨fun h φ ↦ h ⟨φ.toContinuousLinearMap, Submodule.subset_span <| by simp⟩,
    fun h ⟨φ, hφ⟩ ↦ ?_⟩
  simp only [fromEₗ_apply_apply]
  induction hφ using Submodule.span_induction with
  | mem φ hφ => obtain ⟨φ, hφ, rfl⟩ := hφ; exact h φ
  | zero => exact h 0
  | add φ ψ hφ hψ ihφ ihψ => simpa using ihφ.add ihψ
  | smul a φ hφ ihφ => simpa using ihφ.const_smul a

-- ugh, `WeakBilin` has some nasty defeq abuse.
-- we should get this out of tactic mode as a proof.
private noncomputable def weakEUniformEquiv (r : ℝ) :
    (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r : Set σ(M, P)) ≃ᵤ
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) := by
  let e : (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r : Set σ(M, P)) ≃
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) :=
    { toFun := Subtype.map ((weakEEquiv M P).symm ∘ ofUltraweak) fun _ ↦ id
      invFun := Subtype.map (toUltraweak ℂ P ∘ weakEEquiv M P) (by simp)
      left_inv _ := by ext; simp
      right_inv _ := by ext; simp }
  have := isCompact_iff_compactSpace.mp <| isCompact_closedBall ℂ P (0 : M) r
  refine Continuous.uniformOfEquivCompactToT2 e ?_
  rw [continuous_induced_rng, Function.comp_def]
  refine WeakBilin.continuous_of_continuous_eval _ fun ⟨φ, hφ⟩ ↦ ?_
  exact (map_continuous φ).comp continuous_subtype_val

private lemma isCompact_weakE_closedBall (r : ℝ) :
    IsCompact (weakEEquiv M P ⁻¹' Metric.closedBall (0 : M) r) := by
  have := Ultraweak.isCompact_closedBall ℂ P (0 : M) r
  rw [isCompact_iff_compactSpace] at this ⊢
  exact weakEUniformEquiv M P r |>.toHomeomorph.compactSpace

private lemma uniformContinuousOn_toUltraweak_comp_weakEEquiv (r : ℝ) :
    UniformContinuousOn (toUltraweak ℂ P ∘ weakEEquiv M P)
      (weakEEquiv M P ⁻¹' Metric.closedBall (0 : M) r) := by
  rw [uniformContinuousOn_iff_restrict]
  exact uniformContinuous_subtype_val.comp (weakEUniformEquiv M P r).symm.uniformContinuous

private lemma mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall (r : ℝ) :
    Set.MapsTo ((weakEEquiv M P).symm ∘ ofUltraweak (𝕜 := ℂ) (P := P))
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r)
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) :=
  fun x hx ↦ (weakEUniformEquiv M P r ⟨x, hx⟩).2

/-- A bounded filter `l` in `σ(M, P)` is cauchy if and only if `map φ l` is cauchy in `ℂ`
for every positive continuous linear functional `φ`. -/
lemma cauchy_of_forall_posCLM_cauchy_map {l : Filter σ(M, P)} {r : ℝ}
    (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r))
    (hl : ∀ φ : σ(M, P) →P[ℂ] ℂ, Cauchy (map φ l)) :
    Cauchy l := by
  have key : Cauchy (map ((weakEEquiv M P).symm ∘ ofUltraweak) l) := by
    rw [cauchy_weakE_iff_forall_posCLM]
    simpa [Function.comp_def]
  have hlr' : map ((weakEEquiv M P).symm ∘ ofUltraweak) l ≤
      𝓟 (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) :=
    map_mono hlr |>.trans <|
      mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall M P r |>.tendsto
  simpa using key.map_of_le
    (uniformContinuousOn_toUltraweak_comp_weakEEquiv M P r) hlr'

/-- A bounded filter `l` in `σ(M, P)` is cauchy if and only if `map φ l` is cauchy in `ℂ`
for every positive continuous linear functional `φ`. -/
lemma cauchy_of_forall_posCLM_cauchy_map' {l : Filter σ(M, P)} {s : Set M}
    (hs : IsBounded s) (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' s))
    (hl : ∀ φ : σ(M, P) →P[ℂ] ℂ, Cauchy (map φ l)) :
    Cauchy l := by
  obtain ⟨r, hr⟩ := hs |>.subset_closedBall 0
  replace hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r) := hlr.trans <| by simpa
  have key : Cauchy (map ((weakEEquiv M P).symm ∘ ofUltraweak) l) := by
    rw [cauchy_weakE_iff_forall_posCLM]
    simpa [Function.comp_def]
  have hlr' : map ((weakEEquiv M P).symm ∘ ofUltraweak) l ≤
      𝓟 (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) :=
    map_mono hlr |>.trans <|
      mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall M P r |>.tendsto
  simpa using key.map_of_le
    (uniformContinuousOn_toUltraweak_comp_weakEEquiv M P r) hlr'

-- this proof is totally gross
lemma tendsto_of_forall_posCLM {α : Type*} [TopologicalSpace α]
    {l : Filter α} (x : σ(M, P)) {f : α → σ(M, P)} {r : ℝ}
    (hfl : Tendsto f l (𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r)))
    (hf : ∀ φ : σ(M, P) →P[ℂ] ℂ, Tendsto (fun m ↦ φ (f m)) l (𝓝 (φ x))) :
    Tendsto f l (𝓝 x) := by
  by_cases! h_bot : l = ⊥
  · simp [h_bot]
  have key : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓝 ((weakEEquiv M P).symm (ofUltraweak x))) := by
    rw [tendsto_weakE_iff_forall_posCLM]
    simpa [Function.comp_def]
  have hfl' : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓟 (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r))) :=
    map_mono hfl |>.trans <|
      mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall M P r |>.tendsto
  have := (uniformContinuousOn_toUltraweak_comp_weakEEquiv M P r).continuousOn
  have hx : (weakEEquiv M P).symm (ofUltraweak x) ∈
      weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r) :=
    isCompact_weakE_closedBall M P r |>.isClosed.mem_of_tendsto key <| by
      simpa using hfl'
  have := this _ hx |>.tendsto
  have key2 : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓝[weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)]
        ((weakEEquiv M P).symm (ofUltraweak x))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨key, by simpa using hfl'⟩
  simpa using this.comp key2

end Ultraweak
