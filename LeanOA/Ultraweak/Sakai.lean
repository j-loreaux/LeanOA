module

public import LeanOA.Ultraweak.Normal
public import LeanOA.Ultraweak.ClosedSubspace
public import LeanOA.CStarAlgebra.Corner.Order
public import LeanOA.Ultraweak.FiniteSpectrum
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

@[expose] public section

/-! # Sakai's theorem: normal positive functionals are ultraweakly continuous

Let `M` be a W⋆-algebra with predual `P`. This file proves Sakai 1.13.2: a positive linear
functional `φ` on `M` which is normal (in the weak sense that it preserves suprema of directed
sets of projections) is ultraweakly continuous.

## Main declarations

+ `Ultraweak.continuous_of_norm_sq_le`: a functional dominated by the seminorm
  `x ↦ ψ (star x * x) ^ (1 / 2)` of an ultraweakly continuous positive functional `ψ` is
  ultraweakly continuous.
+ `Ultraweak.continuous_of_scottContinuousOn`: **Sakai 1.13.2**.
-/

open scoped Ultraweak ComplexOrder Topology NNReal InnerProductSpace
open Filter Set Metric

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace Ultraweak

include P in
/-- If a norm continuous functional `ω` on `M` satisfies `‖ω x‖ ^ 2 ≤ C * ‖ψ (star x * x)‖`
for some ultraweakly continuous positive functional `ψ`, then `ω` is ultraweakly continuous.

The proof proceeds via the GNS construction for `ψ`: `ω` factors through a bounded functional on
the GNS space of `ψ`, which by the Riesz representation theorem is the inner product with some
vector. Approximating this vector by (the images of) elements `y` of `M` shows that `ω` is a norm
limit of the ultraweakly continuous functionals `x ↦ ψ (star y * x)`. -/
theorem continuous_of_norm_sq_le (ψ : M →ₚ[ℂ] ℂ)
    (hψ : Continuous fun x : σ(M, P) ↦ ψ (ofUltraweak x)) (ω : StrongDual ℂ M) (C : ℝ)
    (hω : ∀ x, ‖ω x‖ ^ 2 ≤ C * ‖ψ (star x * x)‖) :
    Continuous fun x : σ(M, P) ↦ ω (ofUltraweak x) := by
  set C' := √(max C 0)
  /- `‖ω x‖ ≤ C' * ‖x‖` in the GNS (semi)norm. -/
  have hbound (x : M) : ‖ω x‖ ≤ C' * ‖ψ.toPreGNS x‖ := by
    rw [ψ.preGNS_norm_def', ψ.ofPreGNS_toPreGNS, ← Real.sqrt_mul' _ (norm_nonneg _),
      Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact (hω x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  /- `ω` defines a continuous functional on the GNS space, which is the inner product with
  some `η`. -/
  let ω₀ : ψ.PreGNS →L[ℂ] ℂ :=
    (ω.toLinearMap ∘ₗ ψ.ofPreGNS.toLinearMap).mkContinuous C' fun x ↦ by
      simpa using hbound (ψ.ofPreGNS x)
  let ω₁ : StrongDual ℂ ψ.GNS := ω₀.extend UniformSpace.Completion.toComplL
  have hω₁ (x : M) : ω₁ (ψ.toPreGNS x : ψ.GNS) = ω x := by
    have := ω₀.extend_eq (e := UniformSpace.Completion.toComplL)
      UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _)
      (ψ.toPreGNS x)
    simpa [ω₀] using this
  set η := (InnerProductSpace.toDual ℂ ψ.GNS).symm ω₁
  have hη (x : M) : ⟪η, (ψ.toPreGNS x : ψ.GNS)⟫_ℂ = ω x := by
    rw [InnerProductSpace.toDual_symm_apply, hω₁]
  /- `ω` lies in the norm closure of the ultraweakly continuous functionals. -/
  let ψL : StrongDual ℂ M := ψ.toContinuousLinearMap
  set s := √‖ψL‖
  have hj (x : M) : ‖(ψ.toPreGNS x : ψ.GNS)‖ ≤ s * ‖x‖ := by
    rw [UniformSpace.Completion.norm_coe, ψ.preGNS_norm_def', ψ.ofPreGNS_toPreGNS,
      ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (norm_nonneg _)]
    refine Real.sqrt_le_sqrt <| (ψL.le_opNorm _).trans_eq ?_
    rw [CStarRing.norm_star_mul_self, sq]
  refine (isClosed_setOf_continuous (P := P)).closure_subset <|
    Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  /- Approximate `η` within `ε / (s + 1)` by the image of some `y : M`. -/
  obtain ⟨z, hz⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt η
    (show 0 < ε / (s + 1) by positivity)
  set y := ψ.ofPreGNS z
  have hy : ‖η - (ψ.toPreGNS y : ψ.GNS)‖ < ε / (s + 1) := by
    simpa [y, dist_eq_norm] using hz
  let g : StrongDual ℂ M := ψL ∘L ContinuousLinearMap.mul ℂ M (star y)
  refine ⟨g, hψ.comp (continuous_const_mul (toUltraweak ℂ P (star y))), ?_⟩
  rw [dist_eq_norm]
  set r := ‖η - (ψ.toPreGNS y : ψ.GNS)‖
  refine (ContinuousLinearMap.opNorm_le_bound (ω - g) (show 0 ≤ r * s by positivity)
    fun x ↦ ?_).trans_lt ?_
  · have : (ω - g) x = ⟪η - (ψ.toPreGNS y : ψ.GNS), (ψ.toPreGNS x : ψ.GNS)⟫_ℂ := by
      rw [inner_sub_left, hη, UniformSpace.Completion.inner_coe, ψ.preGNS_inner_def]
      simp [g, ψL]
    rw [this, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hj x) (norm_nonneg _))
  · calc r * s ≤ r * (s + 1) := by gcongr; linarith
      _ < ε := by rwa [lt_div_iff₀ (by positivity)] at hy

/-! ### Auxiliary lemmas for Sakai 1.13.2 -/

/-- Nonnegative complex numbers are real, so they are totally ordered. -/
private lemma _root_.Complex.le_of_not_lt_of_nonneg {a b : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ¬ a < b) : b ≤ a := by
  rw [Complex.le_def] at ha hb ⊢
  rw [Complex.lt_def] at h
  refine ⟨?_, by simp_all⟩
  by_contra! h'
  exact h ⟨h', by simp_all⟩

omit [StarOrderedRing M] in
/-- If a positive functional `φ` is Scott continuous on a family `D` of sets, then along a
nonempty directed `d ∈ D`, `φ` tends to its value at the supremum of `d`. -/
lemma tendsto_of_scottContinuousOn {φ : M →ₚ[ℂ] ℂ} {D : Set (Set M)}
    (hφ : ScottContinuousOn D φ) {d : Set M} (hd : d ∈ D) (hne : d.Nonempty)
    (hdir : DirectedOn (· ≤ ·) d) {e : M} (he : IsLUB d e) :
    Tendsto (fun q : d ↦ φ (q : M)) atTop (𝓝 (φ e)) := by
  refine tendsto_atTop_isLUB ((OrderHomClass.mono φ).comp (Subtype.mono_coe _)) ?_
  change IsLUB (Set.range (φ ∘ Subtype.val)) _
  rw [Set.range_comp, Subtype.range_coe]
  exact hφ hd hne hdir he

/-- The positive linear map `x ↦ a * x * a` for a selfadjoint `a`. -/
noncomputable def conjugatePLM {a : M} (ha : IsSelfAdjoint a) : M →ₚ[ℂ] M :=
  .mk₀ (LinearMap.mulLeftRight ℂ (a, a)) fun x hx ↦ by
    simpa [ha.star_eq] using star_left_conjugate_nonneg hx a

@[simp]
lemma conjugatePLM_apply {a : M} (ha : IsSelfAdjoint a) (x : M) :
    conjugatePLM ha x = a * x * a :=
  rfl

/-- If `q ≤ 1 - p` for projections `p` and `q`, then `p * q = 0`. -/
lemma _root_.IsStarProjection.mul_eq_zero_of_le_one_sub {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : q ≤ 1 - p) : p * q = 0 := by
  have h₁ : q * (1 - p) = q := (hq.le_iff_mul_eq_left hp.one_sub).mp h
  have h₂ : q * p = 0 := by
    rw [mul_sub, mul_one] at h₁
    exact sub_eq_self.mp h₁
  simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h₂)

include P in
/-- For a normal positive functional `φ`, there is a maximal projection `p₀` for which
`x ↦ φ (x * p₀)` is ultraweakly continuous. -/
lemma exists_maximal_continuous_mul_right {φ : M →ₚ[ℂ] ℂ}
    (hφ : ScottContinuousOn {d : Set M | (∀ q ∈ d, IsStarProjection q) ∧ IsChain (· ≤ ·) d} φ) :
    ∃ p₀, Maximal (fun p ↦ IsStarProjection p ∧
      Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x * p)) p₀ := by
  let _ := WStarAlgebra.instCCPO M P
  let φL : StrongDual ℂ M := φ.toContinuousLinearMap
  /- `F a` is the functional `x ↦ φ (x * a)`. -/
  let F (a : M) : StrongDual ℂ M := φL ∘L (ContinuousLinearMap.mul ℂ M).flip a
  have hF (a x : M) : F a x = φ (x * a) := rfl
  refine zorn_le₀ _ fun c hc hchain ↦ ?_
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, ⟨.zero _, by simpa using continuous_const⟩, by simp⟩
  have hdir := hchain.directedOn
  have hdp (q) (hq : q ∈ c) : IsStarProjection q := (hc hq).1
  have he := hdir.isLUB_csSup hne ⟨1, fun q hq ↦ (hdp q hq).le_one⟩
  set e := sSup c
  have hep : IsStarProjection e := isStarProjection_of_isLUB (P := P) hne hdir hdp he
  refine ⟨e, ⟨hep, ?_⟩, fun q hq ↦ he.1 hq⟩
  /- `F q` tends to `F e` in norm, since `‖F (e - q)‖ ^ 2 ≤ ‖φ‖ * ‖φ (e - q)‖`. -/
  have : Nonempty c := hne.to_subtype
  have : IsDirectedOrder c := ⟨hdir.directed_val⟩
  have hφe : Tendsto (fun q : c ↦ φ (e - q)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := φ e)).sub
      (tendsto_of_scottContinuousOn hφ ⟨hdp, hchain⟩ hne hdir he)
    simpa [map_sub] using this
  have h₀ : Tendsto (fun q : c ↦ √(‖φL‖ * ‖φ (e - q)‖)) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun q : c ↦ ‖φL‖ * ‖φ (e - q)‖) atTop (𝓝 0) := by
      simpa using (tendsto_norm_zero.comp hφe).const_mul ‖φL‖
    have := (Real.continuous_sqrt.tendsto 0).comp h₁
    simpa only [Function.comp_def, Real.sqrt_zero] using this
  have hFe : Tendsto (fun q : c ↦ F q) atTop (𝓝 (F e)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun q ↦ ?_) h₀
    have hr : IsStarProjection (e - q) := (hdp q q.2).le_iff_sub hep |>.mp (he.1 q.2)
    set r := e - (q : M)
    have hFr : F q - F e = -F r := by ext x; simp [hF, r, mul_sub]
    rw [hFr, norm_neg]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
    rw [hF]
    /- By Cauchy–Schwarz, `‖φ (x * r)‖ ^ 2 ≤ ‖φ (x * star x)‖ * ‖φ r‖`. -/
    have hCS : ‖φ (x * r)‖ ^ 2 ≤ ‖φL‖ * ‖φ r‖ * ‖x‖ ^ 2 := by
      have := PositiveLinearMap.norm_map_mul_star_sq_le φ x r
      rw [hr.isSelfAdjoint.star_eq, hr.isIdempotentElem.eq] at this
      refine this.trans ?_
      have : ‖φ (x * star x)‖ ≤ ‖φL‖ * ‖x‖ ^ 2 :=
        calc ‖φ (x * star x)‖ = ‖φL (x * star x)‖ := rfl
          _ ≤ ‖φL‖ * ‖x * star x‖ := φL.le_opNorm _
          _ = ‖φL‖ * ‖x‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, sq]
      nlinarith [norm_nonneg (φ r), norm_nonneg (φ (x * star x))]
    calc ‖φ (x * r)‖ = √(‖φ (x * r)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(‖φL‖ * ‖φ r‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hCS
      _ = √(‖φL‖ * ‖φ r‖) * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  exact (isClosed_setOf_continuous (P := P)).mem_of_tendsto hFe
    (.of_forall fun q ↦ (hc q.2).2)

include P in
/-- For a nonzero projection `p` and a positive functional `φ`, there is an ultraweakly continuous
positive functional `ψ` with `φ p < ψ p`. -/
lemma exists_lt_of_ne_zero (φ : M →ₚ[ℂ] ℂ) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ ψ : M →ₚ[ℂ] ℂ, (Continuous fun x : σ(M, P) ↦ ψ (ofUltraweak x)) ∧ φ p < ψ p := by
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : σ(M, P) →P[ℂ] ℂ, ψ₀ (toUltraweak ℂ P p) ≠ 0 := by
    by_contra! h
    exact hp0 (eq_zero_of_forall_positiveCLM (toUltraweak ℂ P p) h)
  let ψ₁ : M →ₚ[ℂ] ℂ := (ψ₀.comp (toUltraweakPosCLM P)).toPositiveLinearMap
  have hψ₁ : Continuous fun x : σ(M, P) ↦ ψ₁ (ofUltraweak x) := map_continuous ψ₀
  have hpos : 0 < ψ₁ p := lt_of_le_of_ne (map_nonneg ψ₁ hp.nonneg) (Ne.symm hψ₀)
  have hφp : 0 ≤ φ p := map_nonneg φ hp.nonneg
  rw [Complex.lt_def] at hpos
  rw [Complex.le_def] at hφp
  obtain ⟨n, hn⟩ := exists_nat_gt ((φ p).re / (ψ₁ p).re)
  have hsmul (x : M) : (n • ψ₁) x = (n : ℂ) * ψ₁ x := by
    rw [← nsmul_eq_mul]
    rfl
  refine ⟨n • ψ₁, (continuous_const.mul hψ₁).congr fun x ↦ (hsmul _).symm, ?_⟩
  rw [Complex.lt_def, hsmul]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero]
  refine ⟨by rwa [div_lt_iff₀ hpos.1] at hn, ?_⟩
  rw [← hφp.2, ← hpos.2]
  simp

include P in
/-- If `φ` and `ψ` are normal positive functionals and `φ p < ψ p` for a projection `p`, then
there is a nonzero subprojection `p₁ ≤ p` such that `φ q < ψ q` for every nonzero
subprojection `q ≤ p₁`. -/
lemma exists_forall_lt {φ ψ : M →ₚ[ℂ] ℂ}
    (hφ : ScottContinuousOn {d : Set M | (∀ q ∈ d, IsStarProjection q) ∧ IsChain (· ≤ ·) d} φ)
    (hψ : ScottContinuousOn {d : Set M | (∀ q ∈ d, IsStarProjection q) ∧ IsChain (· ≤ ·) d} ψ)
    {p : M} (hp : IsStarProjection p) (hlt : φ p < ψ p) :
    ∃ p₁, IsStarProjection p₁ ∧ p₁ ≠ 0 ∧ p₁ ≤ p ∧
      ∀ q, IsStarProjection q → q ≠ 0 → q ≤ p₁ → φ q < ψ q := by
  by_contra! h
  let _ := WStarAlgebra.instCCPO M P
  /- By Zorn's lemma, there is a maximal subprojection `q₀ ≤ p` with `ψ q₀ ≤ φ q₀`. -/
  let s : Set M := {q | IsStarProjection q ∧ q ≤ p ∧ ψ q ≤ φ q}
  obtain ⟨q₀, ⟨hq₀, hq₀p, hq₀le⟩, hmax⟩ := zorn_le₀ s fun c hc hchain ↦ by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, ⟨.zero _, hp.nonneg, by simp⟩, by simp⟩
    have hdir := hchain.directedOn
    have hdp (q) (hq : q ∈ c) : IsStarProjection q := (hc hq).1
    have he := hdir.isLUB_csSup hne ⟨p, fun q hq ↦ (hc hq).2.1⟩
    have hep := isStarProjection_of_isLUB (P := P) hne hdir hdp he
    refine ⟨sSup c, ⟨hep, he.2 fun q hq ↦ (hc hq).2.1, ?_⟩, fun q hq ↦ he.1 hq⟩
    have : Nonempty c := hne.to_subtype
    have : IsDirectedOrder c := ⟨hdir.directed_val⟩
    exact le_of_tendsto_of_tendsto' (tendsto_of_scottContinuousOn hψ ⟨hdp, hchain⟩ hne hdir he)
      (tendsto_of_scottContinuousOn hφ ⟨hdp, hchain⟩ hne hdir he) fun q ↦ (hc q.2).2.2
  /- Since `φ p < ψ p`, we have `q₀ ≠ p`, so `p - q₀` is a nonzero projection, and it has a
  nonzero subprojection `q` with `ψ q ≤ φ q`. But then `q₀ + q` contradicts maximality. -/
  have hq₀ne : q₀ ≠ p := by
    rintro rfl
    exact hq₀le.not_gt hlt
  have hr : IsStarProjection (p - q₀) := (hq₀.le_iff_sub hp).mp hq₀p
  obtain ⟨q, hq, hq0, hqr, hnlt⟩ :=
    h (p - q₀) hr (sub_ne_zero.mpr hq₀ne.symm) (sub_le_self _ hq₀.nonneg)
  have hqle : ψ q ≤ φ q :=
    Complex.le_of_not_lt_of_nonneg (map_nonneg φ hq.nonneg) (map_nonneg ψ hq.nonneg) hnlt
  have horth : q₀ * q = 0 :=
    hq₀.mul_eq_zero_of_le_one_sub hq (hqr.trans (sub_le_sub_right hp.le_one _))
  have hsum : q₀ + q ∈ s :=
    ⟨hq₀.add hq horth, le_sub_iff_add_le'.mp hqr, by simpa using add_le_add hq₀le hqle⟩
  have := hmax hsum (le_add_of_nonneg_right hq.nonneg)
  exact hq0 (le_antisymm (by simpa using this) hq.nonneg)

open IsStarProjection in
include P in
/-- If `φ q < ψ q` for every nonzero subprojection `q` of a projection `p`, then `φ a ≤ ψ a` for
every nonnegative `a` in the corner `p * M * p`. This uses that `p * M * p` is a W⋆-algebra in which
nonnegative elements are norm limits of nonnegative combinations of projections. -/
lemma map_le_map_of_forall_lt {φ ψ : M →ₚ[ℂ] ℂ} {p : M} (hp : IsStarProjection p)
    (h : ∀ q, IsStarProjection q → q ≠ 0 → q ≤ p → φ q < ψ q) {a : M} (ha : 0 ≤ a)
    (hpa : p * a * p = a) : φ a ≤ ψ a := by
  have : CStarAlgebra.FiniteSpectrum hp.Corner :=
    CStarAlgebra.finiteSpectrum_of_predual (P := Ultraweak.Subpredual P (hp.cornerSubmodule ℂ))
  /- The inclusion of the corner `p * M * p` into `M` is positive, and since the corner is FS,
  it suffices to compare `φ` and `ψ` on the projections of the corner, which are exactly the
  projections `q ≤ p` of `M`. -/
  let ι : hp.Corner →ₚ[ℂ] M :=
    .mk₀ { toFun := (↑), map_add' := Corner.coe_add, map_smul' := Corner.coe_smul }
      fun _ ↦ Corner.zero_le_coe.mpr
  have ha' : 0 ≤ Corner.mk hp a hpa := by rwa [← Corner.zero_le_coe, Corner.coe_mk]
  refine PositiveLinearMap.le_of_le_on_isStarProjection (φ.comp ι) (ψ.comp ι) (fun q hq ↦ ?_) ha'
  change φ (q : M) ≤ ψ (q : M)
  have hq' : IsStarProjection (q : M) := Corner.isStarProjection_coe_iff.mpr hq
  by_cases hq0 : (q : M) = 0
  · simp [hq0]
  · exact (h q hq' hq0 (Corner.coe_le_of_isStarProjection hq)).le

include P in
/-- **Sakai 1.13.2**, in its strongest form: a positive linear functional on a W⋆-algebra which
preserves suprema of chains of projections is ultraweakly continuous. -/
theorem continuous_of_scottContinuousOn_chains (φ : M →ₚ[ℂ] ℂ)
    (hφ : ScottContinuousOn {d : Set M | (∀ q ∈ d, IsStarProjection q) ∧ IsChain (· ≤ ·) d} φ) :
    Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x) := by
  /- Let `p₀` be maximal among projections `p` for which `x ↦ φ (x * p)` is ultraweakly
  continuous. It suffices to show that `p₀ = 1`. -/
  obtain ⟨p₀, ⟨hp₀, hc₀⟩, hmax⟩ := exists_maximal_continuous_mul_right (P := P) hφ
  suffices p₀ = 1 by simpa [this] using hc₀
  by_contra hne
  /- Otherwise, there is an ultraweakly continuous positive `ψ` with `φ (1 - p₀) < ψ (1 - p₀)`,
  and a nonzero projection `p₁ ≤ 1 - p₀` such that `φ q < ψ q` for all nonzero `q ≤ p₁`. -/
  obtain ⟨ψ, hψc, hlt⟩ :=
    exists_lt_of_ne_zero (P := P) φ hp₀.one_sub (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨p₁, hp₁, hp₁0, hp₁le, hall⟩ := exists_forall_lt (P := P) hφ
    (scottContinuous_of_continuous (P := P) ψ hψc).scottContinuousOn hp₀.one_sub hlt
  /- With `ψ' := ψ (p₁ * · * p₁)`, which is ultraweakly continuous, we have
  `‖φ (x * p₁)‖ ^ 2 ≤ ‖φ 1‖ * ‖φ (p₁ * (star x * x) * p₁)‖ ≤ ‖φ 1‖ * ‖ψ' (star x * x)‖`,
  so `x ↦ φ (x * p₁)` is ultraweakly continuous. -/
  let ψ' : M →ₚ[ℂ] ℂ := ψ.comp (conjugatePLM hp₁.isSelfAdjoint)
  have hψ'c : Continuous fun x : σ(M, P) ↦ ψ' (ofUltraweak x) :=
    hψc.comp ((continuous_mul_const (toUltraweak ℂ P p₁)).comp
      (continuous_const_mul (toUltraweak ℂ P p₁)))
  let ω : StrongDual ℂ M := φ.toContinuousLinearMap ∘L (ContinuousLinearMap.mul ℂ M).flip p₁
  have hωc := continuous_of_norm_sq_le (P := P) ψ' hψ'c ω ‖φ 1‖ fun x ↦ by
    have h₁ := PositiveLinearMap.norm_map_star_mul_sq_le φ 1 (x * p₁)
    have hnn : 0 ≤ p₁ * (star x * x) * p₁ := by
      simpa [hp₁.isSelfAdjoint.star_eq, mul_assoc] using
        star_left_conjugate_nonneg (star_mul_self_nonneg x) p₁
    have h₂ : φ (p₁ * (star x * x) * p₁) ≤ ψ (p₁ * (star x * x) * p₁) :=
      map_le_map_of_forall_lt (P := P) hp₁ hall hnn
        (by simp [← mul_assoc, hp₁.isIdempotentElem.eq, mul_assoc _ p₁ p₁])
    have h₃ := CStarAlgebra.norm_le_norm_of_le_of_nonneg h₂ (map_nonneg φ hnn)
    simp only [star_one, one_mul, star_mul, hp₁.isSelfAdjoint.star_eq, ← mul_assoc] at h₁
    simp only [ω, ψ', ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
      PositiveLinearMap.toContinuousLinearMap_apply, PositiveLinearMap.comp_apply]
    refine h₁.trans <| mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa [mul_assoc] using h₃
  /- Hence `x ↦ φ (x * (p₀ + p₁))` is ultraweakly continuous, contradicting maximality. -/
  have horth : p₀ * p₁ = 0 := hp₀.mul_eq_zero_of_le_one_sub hp₁ hp₁le
  have hcont : Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x * (p₀ + p₁)) :=
    (hc₀.add hωc).congr fun x ↦ by simp [mul_add, ω]
  have := hmax ⟨hp₀.add hp₁ horth, hcont⟩ (le_add_of_nonneg_right hp₁.nonneg)
  exact hp₁0 (le_antisymm (by simpa using this) hp₁.nonneg)

include P in
/-- **Sakai 1.13.2**: a positive linear functional on a W⋆-algebra which is normal (in the sense
that it preserves suprema of directed sets of projections) is ultraweakly continuous. -/
theorem continuous_of_scottContinuousOn (φ : M →ₚ[ℂ] ℂ)
    (hφ : ScottContinuousOn {d : Set M | ∀ q ∈ d, IsStarProjection q} φ) :
    Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x) :=
  continuous_of_scottContinuousOn_chains φ <| hφ.mono fun _ hd ↦ hd.1

include P in
/-- A positive linear functional on a W⋆-algebra which preserves suprema of chains of projections
is normal, i.e., it preserves suprema of all directed sets. Note that the statement does not involve
the predual, but its proof uses the existence of one. -/
theorem scottContinuous_of_scottContinuousOn_chains (φ : M →ₚ[ℂ] ℂ)
    (hφ : ScottContinuousOn {d : Set M | (∀ q ∈ d, IsStarProjection q) ∧ IsChain (· ≤ ·) d} φ) :
    ScottContinuous φ :=
  scottContinuous_of_continuous (P := P) φ (continuous_of_scottContinuousOn_chains φ hφ)

end Ultraweak
