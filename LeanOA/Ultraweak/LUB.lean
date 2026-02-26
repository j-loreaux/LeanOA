import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace
import LeanOA.ComplexOrder
import LeanOA.Mathlib.Algebra.Order.Star.Basic
import LeanOA.Mathlib.Analysis.Complex.Basic
import LeanOA.CFC


variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

namespace Ultraweak

open scoped ComplexOrder

variable (M P)

open PositiveContinuousLinearMap in
/-- Linear combinations of ultraweakly continuous positive linear functionals. -/
private noncomputable def E : Submodule ℂ (StrongDual ℂ σ(M, P)) :=
  Submodule.span ℂ (Set.range toContinuousLinearMap)

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

set_option backward.isDefEq.respectTransparency false in
open Filter in
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

open Filter in
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

open scoped ComplexStarModule

set_option backward.isDefEq.respectTransparency false in
/-- A set in a non-unital C⋆-algebra which is bounded above and below is
bounded in norm. -/
lemma isBounded_of_bddAbove_of_bddBelow {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {s : Set A} (hbd : BddAbove s) (hbd' : BddBelow s) :
    Bornology.IsBounded s := by
  obtain (rfl | hs) := s.eq_empty_or_nonempty
  · simp
  obtain ⟨x₀, hx₀⟩ := hs
  rw [Metric.isBounded_iff_subset_closedBall x₀]
  obtain ⟨a, ha⟩ := hbd'
  obtain ⟨b, hb⟩ := hbd
  use max ‖ℜ (a - x₀)‖ ‖ℜ (b - x₀)‖
  intro x hx
  have : IsSelfAdjoint (x - x₀) := by
    simp only [← imaginaryPart_eq_zero_iff, map_sub, sub_eq_zero]
    rw [imaginaryPart_eq_of_le (hb hx),
      imaginaryPart_eq_of_le (hb hx₀)]
  simp only [Metric.mem_closedBall, dist_eq_norm]
  rw [← this.coe_realPart]
  simp only [map_sub, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
  apply IsSelfAdjoint.norm_le_max_of_le_of_le (by cfc_tac)
  all_goals simpa using realPart_mono (by aesop)

open Filter Topology Set in
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
    exact Tendsto.cauchy_map <| tendsto_atTop_ciSup (hφ.comp (Subtype.mono_coe s)) <| by
      simpa [← Function.comp_def, Set.range_comp]
        using (OrderHomClass.mono φ |>.map_bddAbove hbd)
  /- Since the closed ball is compact (and therefore complete) and this cauchy net is
  eventually within it, it converges to some element `x`. -/
  obtain ⟨x, -, hx⟩ := isCompact_closedBall ℂ P (0 : M) r |>.isComplete _ h_cauchy h_map_le
  refine ⟨x, ?_, hx⟩
  /- Since the net is increasing, and the topology on `σ(M, P)` is order closed, the
  limit is the least upper bound. -/
  simpa [setOf] using isLUB_of_tendsto_atTop (β := s) (Subtype.mono_coe s) hx

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

attribute [push] Filter.not_neBot
attribute [push ←] Filter.neBot_iff

open Filter in
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

end Ultraweak
