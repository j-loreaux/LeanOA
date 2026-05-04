module

public import LeanOA.Ultraweak.Uniformity
public import LeanOA.ComplexOrder
public import LeanOA.Mathlib.Algebra.Order.Star.Basic
public import LeanOA.Mathlib.Analysis.Complex.Basic
public import LeanOA.CFC
public import LeanOA.Ultraweak.ContinuousFunctionalCalculus
public import LeanOA.Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import LeanOA.CStarAlgebra.PositiveLinearFunctional
public import LeanOA.Mathlib.Algebra.Order.Star.Conjugate

@[expose] public section

/-! # `σ(M, P)` is a conditionally complete partial order

This file establishes some nice order-theoretic properties of `σ(M, P)`.
Since the order on `σ(M, P)` coincides with the order on `M`, these transfer.
In particular, we show that it:

+ is a conditionally complete partial order (i.e. every nonempty directed set which is bounded above
  has a least upper bound);
+ satisfies `SupConvergenceClass` (monotone functions converge to their supremum)
+ and conjugation preserves suprema

-/


variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

namespace Ultraweak

open scoped ComplexOrder ComplexStarModule Topology
open Filter Set Bornology StarOrderedRing

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
    apply cauchy_of_forall_posCLM_of_eventually (by simpa using h_map_le) fun φ ↦ ?_
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
    then (DirectedOn.exists_isLUB s h.1 h.2.1 h.2.2).choose
    else 0
  isLUB_csSup_of_directed s h_dir h_non hbdd := by
    rw [dif_pos (by grind)]
    exact (DirectedOn.exists_isLUB s h_dir h_non hbdd).choose_spec.1

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
    obtain ⟨u, hu₁, hu₂⟩ := DirectedOn.exists_isLUB s h₂ h₁ ⟨_, hsa.1⟩
    exact hsa.unique hu₁ ▸ hu₂

omit [CompleteSpace P] in
private theorem isLUB_star_right_conjugate_aux (a u : σ(M, P)) (s : Set σ(M, P))
    [IsDirectedOrder s] [Nonempty s] (h : IsLUB s u)
    (h₁ : Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 u))
    (φ : σ(M, P) →P[ℂ] ℂ) :
    Tendsto (fun x : s ↦ φ (a * x)) atTop (𝓝 (φ (a * u))) := by
  /- It clearly suffices to show `x ↦ ‖φ (a * (u - x))‖` tends to zero. -/
  rw [tendsto_iff_norm_sub_tendsto_zero]
  conv => enter [1, x]; rw [norm_sub_rev, ← map_sub, ← mul_sub]
  /- `fun x ↦ u - ↑x` tends to zero since `Subtype.val` tends to `u`.
  And since `φ` is continuous, `fun x ↦ √‖φ (u - x)‖` also tends to zero. -/
  have h₁ : Tendsto (fun x : s ↦ u - x) atTop (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.mpr h₁ |>.neg)
  have h₂ : Tendsto (fun x : s ↦ √‖φ (u - x)‖) atTop (𝓝 0) := by
    have := Real.continuous_sqrt.comp' continuous_norm |>.comp' (map_continuous φ)
    simpa [- map_sub] using this.tendsto _ |>.comp <| h₁
  /- The map `x ↦ √‖φ (a * (u - x) * star a)‖` is eventually bounded because `φ` is norm
  continuous (since it is ultraweakly continuous), and it argument is eventually smaller than the
  nonnegative element `a * (u - x₀) * star a`, where `x₀ ∈ s` is arbitrary. -/
  obtain ⟨c, hcu⟩ : ∃ c, ∀ᶠ (x : s) in atTop, |√‖φ (a * (u - x) * star a)‖| ≤ c := by
    have x₀ : s := Classical.arbitrary s
    let φ' := φ.comp (toUltraweakPosCLM P) |>.toContinuousLinearMap
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
  /- By the Cauchy-Schwarz inequality,
    ‖φ (a * (u - x))‖ ≤ ‖φ (a * √(u - x) * √(u - x))‖
    _ ≤ √‖φ (a * (u - x) * star a)‖ * √‖φ (u - x)‖.
  Since the first factor is bounded and the latter tendsto to zero, the product tends to zero.
  Hence `φ (a * (u - x))` tends to zero by the squeeze theorem. -/
  refine squeeze_zero (fun _ ↦ by positivity) (fun x ↦ ?_) <| bdd_le_mul_tendsto_zero' c hcu h₂
  have hux : 0 ≤ u - x := sub_nonneg.mpr <| h.1 x.prop
  rw [← CFC.sqrt_mul_sqrt_self' (u - x)]
  have := φ.toPositiveLinearMap.cauchy_schwarz_mul_star
    (a * CFC.sqrt (u - x)) (star (CFC.sqrt (u - x)))
  simpa [(CFC.sqrt_nonneg (u - x)).star_eq, mul_assoc]

/-- If `s` is a nonempty directed set which is bounded above with supremum `u`,
then so is `(a * · * star a) '' s`, and its least upper bound is `a * u * star a`. -/
lemma DirectedOn.isLUB_star_right_conjugate (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (h : IsLUB s u) :
    IsLUB (conjOrderHom a '' s) (a * u * star a) := by
  /- Clearly `fun x : s ↦ ↑x` converges to `u`. For any invertible element `b`, since
  `(b * · * star b)` is an order isomorphism, we find that `(b * · * star b) '' s` has
  `b * u * star b` as its least upper bound, and hence `(b * · * star b)` tends to
  `b * u * star b`. And since `(a * · * star a)` is monotone, it suffices to show that this
  converges to `a * u * star a` (along `atTop : Filter ↥s`). -/
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
  /- Since this function has eventually bounded range (eventually bounded below by `a * x₀ * star a`
  for any fixed `x₀ ∈ s`, and bounded above by `a * u * star a`), it suffices to check that for
  any positive continuous linear functional `φ : σ(M, P) →P[ℂ] ℂ` that `fun x ↦ φ (a * x * star a)`
  tends to `φ (a * u * star a)`. -/
  refine tendsto_of_forall_posCLM_of_disjoint ?hbdd fun φ ↦ ?htends
  case hbdd =>
    have x₀ : s := Classical.arbitrary s
    simp only [disjoint_cobounded_iff]
    refine ⟨_, image_mem_map (Ici_mem_atTop x₀), ?_⟩
    rw [← isBounded_image_ofUltraweak]
    apply isBounded_of_bddAbove_of_bddBelow <;> simp only [image_image]
    · refine monotone_ofUltraweak.comp (conjOrderHom a).monotone |>.map_bddAbove ⟨u, h.1⟩ |>.mono ?_
      rintro - ⟨x, hx, rfl⟩
      exact ⟨x.val, x.prop, rfl⟩
    · exact monotone_ofUltraweak.comp (conjOrderHom a).monotone |>.comp (Subtype.mono_coe (· ∈ s))
        |>.map_bddBelow ⟨x₀, fun _ ↦ id⟩
  /- By the previous lemma `fun x ↦ φ (a * x)` and `fun x ↦ φ (x * star a)` tend to `φ (a * u)`
  and `φ (u * star a)`, respectively. -/
  have h₃ : Tendsto (fun x : s ↦ φ (a * x)) atTop (𝓝 (φ (a * u))) :=
    isLUB_star_right_conjugate_aux a u s h h₁ φ
  have h₄ : Tendsto (fun x : s ↦ φ (x * star a)) atTop (𝓝 (φ (u * star a))) := by
    simp_rw +singlePass [tendsto_iff_norm_sub_tendsto_zero, norm_sub_rev,
      ← map_sub, ← mul_sub, ← sub_mul] at h₃ ⊢
    apply h₃.congr fun x ↦ ?_
    convert norm_star (φ ((u - x) * star a))
    rw [← map_star φ, star_mul, star_star, (sub_nonneg.mpr (h.1 x.prop)).star_eq]
  /- Obviously there is some `z : ℂ` so that `z + a` is invertible.
  So we note that `fun x ↦ φ ((z + a) * x * star (z + a))` tends to `(z + a) * u * star (z + a)`
  (because `z + a` is invertible). But at the same time, by expanding the terms out, we see that
  `fun x ↦ z * star z * φ x + star z * φ (a * x) + z * φ (x * star a) + φ (a * x * star a)`.
  The first thre terms converge to `z * star z * φ u + star z * φ (a * u) + z * φ (u * star a)`
  and since the entirety converges to `(z + a) * u * star (z + a)` we obtain the desired convergence
  of `fun x ↦ φ (a * x * star a)` to `φ (a * u * star a)`. -/
  obtain ⟨z, hz⟩ : ∃ z : ℂ, IsUnit (algebraMap ℂ σ(M, P) z + a) := by
    suffices spectrum ℂ (-a) ≠ Set.univ by simpa [Set.ne_univ_iff_exists_notMem, spectrum.mem_iff]
    simpa using spectrum.isCompact (starAlgEquiv M P (-a)) |>.ne_univ
  have key (x : σ(M, P)) : φ (a * x * star a) =
      φ ((algebraMap ℂ σ(M, P) z + a) * x * star (algebraMap ℂ σ(M, P) z + a)) -
      (z * star z * φ x + star z * φ (a * x) + z * φ (x * star a)) := by
    simp [Algebra.algebraMap_eq_smul_one, add_mul, mul_add]
    ring
  simp only [key]
  apply_rules [Tendsto.sub, Tendsto.add, Tendsto.const_mul]
  · exact (map_continuous φ).tendsto _ |>.comp <| h₂ _ hz
  · exact (map_continuous φ).tendsto _ |>.comp <| h₁

end Ultraweak
