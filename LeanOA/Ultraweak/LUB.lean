import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace
import LeanOA.ComplexOrder
import LeanOA.Mathlib.Algebra.Order.Star.Basic
import LeanOA.Mathlib.Analysis.Complex.Basic
import LeanOA.CFC
import LeanOA.Ultraweak.ContinuousFunctionalCalculus
import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LeanOA.CStarAlgebra.PositiveLinearFunctional
import LeanOA.Mathlib.Algebra.Order.Star.Conjugate


variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

namespace Ultraweak

open scoped ComplexOrder ComplexStarModule Topology
open Filter Set Bornology StarOrderedRing

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
    (hs : Bornology.IsBounded s) (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' s))
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

attribute [push] Filter.not_neBot
attribute [push ←] Filter.neBot_iff

-- this proof is totally gross
private lemma tendsto_of_forall_posCLM {α : Type*} [TopologicalSpace α]
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

/-- An increasing net of elements which is bounded above in `σ(M, P)` converges
to its least upper bound.

I'll note that this uses that `σ(M, P)` is an `OrderClosedTopology` to conclude
the element to which is converges is indeed the least upper bound. -/
lemma DirectedOn.exists_isLUB (s : Set σ(M, P)) (hs : DirectedOn (· ≤ ·) s)
    (hnon : s.Nonempty) (hbd : BddAbove s) :
    ∃ x : σ(M, P), IsLUB s x ∧ Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 x) := by
  /- Since `s` is nonempty, we may take the intersection with `Ici x₀` for some
  `x₀ ∈ s`. This set is still directed, but now it is also bounded above and below.
  Hence it is norm bounded. -/
  let ⟨x₀, hx₀⟩ := hnon
  have hbd' : BddAbove (ofUltraweak '' (s ∩ Ici x₀)) :=
    monotone_ofUltraweak.map_bddAbove hbd.inter_of_left
  have hbd'' : BddBelow (ofUltraweak '' (s ∩ Ici x₀)) := by
    use ofUltraweak x₀
    rintro - ⟨x, hx, rfl⟩
    aesop
  obtain ⟨r, hr⟩ := isBounded_of_bddAbove_of_bddBelow hbd' hbd'' |>.subset_closedBall 0
  /- The net `s` of elements is eventually bounded. -/
  have h_map_le : map (Subtype.val : s → σ(M, P)) atTop ≤
      𝓟 (ofUltraweak ⁻¹' Metric.closedBall 0 r) := by
    simp only [le_principal_iff, mem_map]
    refine mem_of_superset (Ici_mem_atTop (⟨x₀, hx₀⟩ : s)) ?_
    intro ⟨x, hx⟩ hxx₀
    simp only [mem_Ici, Subtype.mk_le_mk, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] at hxx₀ ⊢
    simpa using hr ⟨_, ⟨hx, hxx₀⟩, rfl⟩
  /- The subtype `↥s` is directed and nonempty. -/
  have : IsDirectedOrder s := ⟨hs.directed_val⟩
  have : Nonempty s := hnon.to_subtype
  /- To see that the net `s` is cauchy in `σ(M, P)` it suffices to check that for
  any continuous positive linear functional `φ`, applying `φ` to `s` is also cauchy.
  However, since this is a net in `ℂ` which is bounded above, it in fact converges,
  and is therefore cauchy. -/
  have h_cauchy : Cauchy (map ((↑) : s → σ(M, P)) atTop) := by
    apply cauchy_of_forall_posCLM_cauchy_map M P h_map_le fun φ ↦ ?_
    have hφ := OrderHomClass.mono φ
    exact Tendsto.cauchy_map <| tendsto_atTop_ciSup (hφ.comp (Subtype.mono_coe (· ∈ s))) <| by
      simpa [← Function.comp_def, Set.range_comp]
        using (OrderHomClass.mono φ |>.map_bddAbove hbd)
  /- Since the closed ball is compact (and therefore complete) and this cauchy net is
  eventually within it, it converges to some element `x`. -/
  obtain ⟨x, -, hx⟩ := isCompact_closedBall ℂ P (0 : M) r |>.isComplete _ h_cauchy h_map_le
  refine ⟨x, ?_, hx⟩
  /- Since the net is increasing, and the topology on `σ(M, P)` is order closed, the
  limit is the least upper bound. -/
  simpa [setOf] using isLUB_of_tendsto_atTop (β := s) (Subtype.mono_coe (· ∈ s)) hx

/-- `σ(M, P)` is a conditionally complete partial order. Since this is only dependent upon the
order, not the topology, the same is true of `M`. -/
noncomputable instance : ConditionallyCompletePartialOrderSup σ(M, P) where
  sSup s :=
    open Classical in
    if h : DirectedOn (· ≤ ·) s ∧ s.Nonempty ∧ BddAbove s
    then (DirectedOn.exists_isLUB M P s h.1 h.2.1 h.2.2).choose
    else 0
  isLUB_csSup_of_directed s h_dir h_non hbdd := by
    rw [dif_pos (by grind)]
    exact (DirectedOn.exists_isLUB M P s h_dir h_non hbdd).choose_spec.1

/-- An increasing net of elements which is bounded above in `σ(M, P)` converges
to its least upper bound. -/
instance : SupConvergenceClass σ(M, P) where
  tendsto_coe_atTop_isLUB a s hsa := by
    by_cases! h : (atTop : Filter s) = ⊥
    · simp [h]
    rw [atTop_neBot_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    replace h₁ : s.Nonempty := Set.nonempty_coe_sort.mp h₁
    replace h₂ : DirectedOn (· ≤ ·) s := by
      rw [directedOn_iff_directed]
      obtain ⟨h₂⟩ := h₂
      exact h₂
    obtain ⟨u, hu₁, hu₂⟩ := DirectedOn.exists_isLUB M P s h₂ h₁ ⟨_, hsa.1⟩
    exact hsa.unique hu₁ ▸ hu₂




/-- The map `toUltraweak` as a positive continuous linear map. -/
@[simps]
def toUltraweakPosCLM : M →P[ℂ] σ(M, P) where
  toFun m := toUltraweak ℂ P m
  map_add' := by simp
  map_smul' := by simp
  monotone' _ _ := id
  cont := by fun_prop


--- Notes: we should make `toUltraweak_le_toUltraweak_iff` and make a unidirectional version
--- `gcongr`, same for `ofUltraweak`.
--- also, it would be very nice if we could make `a ≤ b → c * a * star c ≤ c * b * star c` a
--- `gcongr` lemma, but we can't right now because the head function is `HMul.hMul · c`, so we
--- would have to bundle the conjugation operation into it's own function, and then it would
--- work.

theorem foo.extracted_1_1 (M P : Type*) [inst : CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Predual ℂ M P] (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (h : IsLUB s u)
    (h₁ : Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 u))
    (φ : σ(M, P) →P[ℂ] ℂ) :
    Tendsto (fun x : s ↦ ‖φ (a * (u - x))‖) atTop (𝓝 0) := by
  have : Nonempty s := hnon.to_subtype
  have : IsDirectedOrder s := directedOn_iff_isDirectedOrder.mp hd
  have h₁ : Tendsto (fun x : s ↦ u - x) atTop (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.mpr h₁ |>.neg)
  have h₂ : Tendsto (fun x : s ↦ √‖φ (u - x)‖) atTop (𝓝 0) := by
    have := Real.continuous_sqrt.comp' continuous_norm |>.comp' (map_continuous φ)
    simpa [- map_sub] using this.tendsto _ |>.comp <| h₁
  obtain ⟨c, hcu⟩ : ∃ c, ∀ᶠ (x : s) in atTop, |√‖φ (a * (u - x) * star a)‖| ≤ c := by
    have x₀ : s := Classical.arbitrary s
    let φ' := (φ.comp (toUltraweakPosCLM M P)).toContinuousLinearMap
    use |√(‖φ'‖ * ‖ofUltraweak (a * (u - x₀.val) * star a)‖)|
    filter_upwards [Ici_mem_atTop x₀] with x (hx : x₀ ≤ x)
    gcongr
    calc
      ‖φ (a * (u - x) * star a)‖ ≤ ‖φ (a * (u - x₀) * star a)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le -- hitting a nail with a nuke
          (map_nonneg φ <| star_right_conjugate_nonneg (by simpa using h.1 x.prop) a)
          (OrderHomClass.mono φ <| star_right_conjugate_le_conjugate (by grw [hx]) a)
      _ = ‖φ' (ofUltraweak (a * (u - ↑x₀) * star a))‖ := by simp [φ']
      _ ≤ ‖φ'‖ * ‖ofUltraweak (a * (u - ↑x₀) * star a)‖ := φ'.le_opNorm _
  have := bdd_le_mul_tendsto_zero' c hcu h₂
  refine squeeze_zero (fun _ ↦ by positivity) (fun x ↦ ?_) this
  have hux : 0 ≤ u - x := sub_nonneg.mpr <| h.1 x.prop
  rw [← CFC.sqrt_mul_sqrt_self' (u - x)]
  have := φ.toPositiveLinearMap.cauchy_schwarz_mul_star
    (a * CFC.sqrt (u - x)) (star (CFC.sqrt (u - x)))
  simpa [(CFC.sqrt_nonneg (u - x)).star_eq, mul_assoc]

theorem foo.extracted_1_2 (M P : Type*) [inst : CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Predual ℂ M P] (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (h : IsLUB s u)
    (h₁ : Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 u))
    (φ : σ(M, P) →P[ℂ] ℂ) :
    Tendsto (fun x : s ↦ ‖φ ((u - x) * a)‖) atTop (𝓝 0) := by
  apply foo.extracted_1_1 M P (star a) u s hd hnon h h₁ φ |>.congr fun x ↦ ?_
  convert norm_star (φ ((u - x) * a))
  rw [← map_star φ, star_mul, (sub_nonneg.mpr (h.1 x.prop)).star_eq]

open Topology
lemma DirectedOn.isLUB_star_right_conjugate (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (h : IsLUB s u) :
    IsLUB (conjOrderHom a '' s) (a * u * star a) := by
  have : Nonempty s := hnon.to_subtype
  have : IsDirectedOrder s := directedOn_iff_isDirectedOrder.mp hd
  have h₁ : Tendsto (· : s → σ(M, P)) atTop (𝓝 u) :=
    tendsto_atTop_isLUB (Subtype.mono_coe (· ∈ s)) <| Subtype.range_coe ▸ h
  have h₂ (b : σ(M, P)) (hb : IsUnit b) :
      Tendsto (fun x : s ↦ b * x * star b) atTop (𝓝 (b * u * star b)) := by
    refine tendsto_atTop_isLUB (conjOrderHom b |>.monotone.comp <| Subtype.mono_coe (· ∈ s)) ?_
    convert h.conjugate_star_right_of_isUnit b hb
    ext
    simp
  suffices Tendsto (fun x : s ↦ a * x * star a) atTop (𝓝 (a * u * star a)) by
    convert isLUB_of_tendsto_atTop (conjOrderHom a |>.monotone.comp <|
      Subtype.mono_coe (· ∈ s)) this
    ext
    simp
  obtain ⟨r, hr⟩ : ∃ r, Tendsto (fun x : s ↦ a * x * star a)
      atTop (𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r)) := by
    simp only [tendsto_principal]
    have x₀ : s := Classical.arbitrary s
    have hbd' : BddBelow ((ofUltraweak ∘ conjOrderHom a) '' (s ∩ Set.Ici x₀)) := by
      use ofUltraweak (a * x₀.val * star a)
      rintro - ⟨x, hx, rfl⟩
      exact star_right_conjugate_le_conjugate hx.2 a
    have hbd'' : BddAbove ((ofUltraweak ∘ conjOrderHom a) '' (s ∩ Set.Ici x₀)) := by
      apply monotone_ofUltraweak.comp (conjOrderHom a).monotone |>.map_bddAbove ⟨u, h.1⟩ |>.mono
      gcongr
      simp
    obtain ⟨r, hr⟩ := isBounded_of_bddAbove_of_bddBelow hbd'' hbd' |>.subset_closedBall 0
    use r
    filter_upwards [Ici_mem_atTop x₀] with x hx
    exact hr ⟨x, ⟨x.prop, hx⟩, rfl⟩
  refine tendsto_of_forall_posCLM M P (a * u * star a) hr fun φ ↦ ?_
  have h₃ : Tendsto (fun x : s ↦ φ (a * x)) atTop (𝓝 (φ (a * u))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    conv =>
      enter [1, x]
      rw [norm_sub_rev, ← map_sub, ← mul_sub]
    exact foo.extracted_1_1 M P a u s hd hnon h h₁ φ
  have h₄ : Tendsto (fun x : s ↦ φ (x * star a)) atTop (𝓝 (φ (u * star a))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    conv =>
      enter [1, x]
      rw [norm_sub_rev, ← map_sub, ← sub_mul]
    exact foo.extracted_1_2 M P (star a) u s hd hnon h h₁ φ
  obtain ⟨z, hz⟩ : ∃ z : ℂ, IsUnit (algebraMap ℂ σ(M, P) z + a) := by
    suffices spectrum ℂ (-a) ≠ Set.univ by simpa [Set.ne_univ_iff_exists_notMem, spectrum.mem_iff]
    simpa using spectrum.isCompact (starAlgEquiv M P (-a)) |>.ne_univ
  have key (x : σ(M, P)) :
      φ (a * x * star a) =
      φ ((algebraMap ℂ σ(M, P) z + a) * x * star (algebraMap ℂ σ(M, P) z + a)) -
        (z * star z * φ x + star z * φ (a * x) + z * φ (x * star a)) := by
    simp [Algebra.algebraMap_eq_smul_one, add_mul, mul_add]
    ring
  simp only [key]
  apply_rules [Tendsto.sub, Tendsto.add, Tendsto.const_mul]
  · exact (map_continuous φ).tendsto _ |>.comp <| h₂ _ hz
  · exact (map_continuous φ).tendsto _ |>.comp <| h₁

end Ultraweak
