module

public import LeanOA.Ultraweak.Normal
public import LeanOA.Ultraweak.ClosedSubspace
public import LeanOA.CStarAlgebra.Corner.Order
public import LeanOA.Ultraweak.FiniteSpectrum
public import LeanOA.Mathlib.Topology.Order.MonotoneConvergence
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

## Implementation notes

The declaration `Ultraweak.continuous_of_norm_sq_le` essentially amounts to a proof that every
ultrastrongly continuous functional is also ultraweakly continuous. Since the ultraweak topology
is weaker than the ultrastrong topology, this shows that the two topologies have the same continuous
linear functionals. Crucially, we avoid developing the ultrastrong topology explicitly here.
-/

open scoped Ultraweak ComplexOrder Topology NNReal InnerProductSpace StarRing
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
  /- `ω` defines a continuous functional `ω₁` on the GNS space, so that `ω = ω₁ ∘ j`, where
  `j : M → ψ.GNS` is the canonical (norm continuous) map. -/
  let ω₀ : ψ.PreGNS →L[ℂ] ℂ :=
    (ω.toLinearMap ∘ₗ ψ.ofPreGNS.toLinearMap).mkContinuous C' fun x ↦ by
      simpa using hbound (ψ.ofPreGNS x)
  let ω₁ : StrongDual ℂ ψ.GNS := ω₀.extend UniformSpace.Completion.toComplL
  let ψL : StrongDual ℂ M := ψ.toContinuousLinearMap
  let j : M →L[ℂ] ψ.GNS :=
    (UniformSpace.Completion.toComplL.toLinearMap ∘ₗ ψ.toPreGNS.toLinearMap).mkContinuous
      √‖ψL‖ fun x ↦ by
        rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, UniformSpace.Completion.coe_toComplL,
          LinearEquiv.coe_coe, UniformSpace.Completion.norm_coe, ψ.preGNS_norm_def',
          ψ.ofPreGNS_toPreGNS, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (norm_nonneg _)]
        refine Real.sqrt_le_sqrt <| (ψL.le_opNorm _).trans_eq ?_
        rw [CStarRing.norm_star_mul_self, sq]
  have hωj : ω = ω₁ ∘L j := by ext x; simp [ω₀, ω₁, j]
  /- By the Riesz representation theorem, `ω₁ = ⟪η, ·⟫` for some `η`, and it suffices to show that
  `x ↦ ⟪η, j x⟫` is ultraweakly continuous. This is a closed condition on `η`, so we may assume
  `η` is the image of some `y : M`, in which case this is `x ↦ ψ (star y * x)`. -/
  obtain ⟨η, hη⟩ := (InnerProductSpace.toDual ℂ ψ.GNS).surjective ω₁
  rw [hωj, ← hη]
  clear hη
  induction η using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_setOf_continuous (P := P) |>.preimage <|
      (ContinuousLinearMap.precomp ℂ j).continuous.comp (InnerProductSpace.toDual ℂ _).continuous
  | ih z =>
    simpa [j, ψ.preGNS_inner_def, Function.comp_def] using
      hψ.comp (continuous_const_mul (toUltraweak ℂ P (star (ψ.ofPreGNS z))))

/-! ### Auxiliary lemmas for Sakai 1.13.2 -/

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
  suffices ∃ p₀, Maximal (· ∈ {p | IsStarProjection p ∧
      Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x * p)}) p₀ by
    simpa only [Set.mem_ofPred_eq] using this
  refine zorn_le₀ _ fun c hc hchain ↦ ?_
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, ⟨.zero _, by simpa using continuous_const⟩, by simp⟩
  have hdir := hchain.directedOn
  have hdp (q) (hq : q ∈ c) : IsStarProjection q := (hc hq).1
  have he := hdir.isLUB_csSup hne ⟨1, fun q hq ↦ (hdp q hq).le_one⟩
  set e := sSup c
  have hep : IsStarProjection e := isStarProjection_of_isLUB (P := P) hne hdir hdp he
  refine ⟨e, ⟨hep, ?_⟩, fun q hq ↦ he.1 hq⟩
  /- `F q` tends to `F e` in norm, since `‖F (e - q)‖ ≤ √‖φ‖ * √‖φ (e - q)‖`. -/
  have : Nonempty c := hne.to_subtype
  have : IsDirectedOrder c := ⟨hdir.directed_val⟩
  have h₀ : Tendsto (fun q : c ↦ √‖φL‖ * √‖φ (e - q)‖) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := φ e)).sub
      (hφ.tendsto_atTop_isLUB ⟨hdp, hchain⟩ hne hdir ((OrderHomClass.mono φ).monotoneOn _) he)
    simpa [map_sub, Function.comp_def] using
      ((continuous_const.mul continuous_norm.sqrt).tendsto _).comp this
  have hFe : Tendsto (fun q : c ↦ F q) atTop (𝓝 (F e)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun q ↦ ?_) h₀
    have hr : IsStarProjection (e - q) := (hdp q q.2).le_iff_sub hep |>.mp (he.1 q.2)
    rw [norm_sub_rev, show F e - F q = F (e - q) by ext; simp [hF, mul_sub]]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
    /- By Cauchy–Schwarz, `‖φ (x * r)‖ ≤ √‖φ (x * star x)‖ * √‖φ r‖` for `r = e - q`. -/
    have hCS := PositiveLinearMap.norm_map_mul_star_le φ x (e - q)
    rw [hr.isSelfAdjoint.star_eq, hr.isIdempotentElem.eq] at hCS
    have hx : √‖φ (x * star x)‖ ≤ √‖φL‖ * ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (norm_nonneg _)]
      gcongr
      exact (φL.le_opNorm _).trans_eq (by rw [CStarRing.norm_self_mul_star, sq])
    calc ‖F (e - q) x‖ ≤ √‖φ (x * star x)‖ * √‖φ (e - q)‖ := hCS
      _ ≤ √‖φL‖ * ‖x‖ * √‖φ (e - q)‖ := by gcongr
      _ = √‖φL‖ * √‖φ (e - q)‖ * ‖x‖ := mul_right_comm ..
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
  obtain ⟨n, hn⟩ := exists_nat_gt (‖φ p‖ / ‖ψ₁ p‖)
  refine ⟨n • ψ₁, map_continuous (n • ψ₀), ?_⟩
  rw [smul_apply, Complex.eq_coe_norm_of_nonneg (map_nonneg φ hp.nonneg),
    Complex.eq_coe_norm_of_nonneg (map_nonneg ψ₁ hp.nonneg), nsmul_eq_mul]
  exact_mod_cast (div_lt_iff₀ (norm_pos_iff.mpr hψ₀)).mp hn

include P in
/-- If `φ` and `ψ` are positive functionals with `ψ` normal, and `φ p < ψ p` for a projection
`p`, then there is a nonzero subprojection `p₁ ≤ p` such that `φ q < ψ q` for every nonzero
subprojection `q ≤ p₁`. -/
lemma exists_forall_lt {φ ψ : M →ₚ[ℂ] ℂ}
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
    /- `ψ (sSup c) = ⨆ q ∈ c, ψ q ≤ φ (sSup c)`, since `ψ q ≤ φ q ≤ φ (sSup c)` for `q ∈ c`. -/
    refine ⟨sSup c, ⟨hep, he.2 fun q hq ↦ (hc hq).2.1, ?_⟩, fun q hq ↦ he.1 hq⟩
    exact (hψ ⟨hdp, hchain⟩ hne hdir he).2 <| forall_mem_image.mpr fun q hq ↦
      (hc hq).2.2.trans <| OrderHomClass.mono φ <| he.1 hq
  /- Since `φ p < ψ p`, we have `q₀ ≠ p`, so `p - q₀` is a nonzero projection, and it has a
  nonzero subprojection `q` with `ψ q ≤ φ q`. But then `q₀ + q` contradicts maximality. -/
  have hq₀ne : q₀ ≠ p := fun h ↦ hq₀le.not_gt (h ▸ hlt)
  have hr : IsStarProjection (p - q₀) := (hq₀.le_iff_sub hp).mp hq₀p
  obtain ⟨q, hq, hq0, hqr, hnlt⟩ :=
    h (p - q₀) hr (sub_ne_zero.mpr hq₀ne.symm) (sub_le_self _ hq₀.nonneg)
  have hqle : ψ q ≤ φ q := by
    grind [Complex.le_def, Complex.lt_def, map_nonneg φ hq.nonneg, map_nonneg ψ hq.nonneg]
  have horth : q ⋆⟂ q₀ :=
    hq₀.one_sub_isStarOrtho.of_le hq.nonneg (hqr.trans (sub_le_sub_right hp.le_one _))
  have hsum : q₀ + q ∈ s :=
    ⟨horth.symm.isStarProjection_add hq₀ hq, le_sub_iff_add_le'.mp hqr,
      by simpa using add_le_add hq₀le hqle⟩
  exact hq0 <| le_antisymm (by simpa using hmax hsum (le_add_of_nonneg_right hq.nonneg)) hq.nonneg

open IsStarProjection in
include P in
/-- If `φ q < ψ q` for every nonzero subprojection `q` of a projection `p`, then `φ ≤ ψ` on the
nonnegative elements `p * a * p` of the corner `p * M * p`. This uses that `p * M * p` is a
W⋆-algebra in which nonnegative elements are norm limits of nonnegative combinations of
projections. -/
lemma map_le_map_of_forall_lt {φ ψ : M →ₚ[ℂ] ℂ} {p : M} (hp : IsStarProjection p)
    (h : ∀ q, IsStarProjection q → q ≠ 0 → q ≤ p → φ q < ψ q) {a : M} (ha : 0 ≤ a) :
    φ (p * a * p) ≤ ψ (p * a * p) := by
  have : WStarAlgebra hp.Corner :=
    .of_predual (P := Ultraweak.Subpredual P (hp.cornerSubmodule ℂ))
  /- The inclusion of the corner `p * M * p` into `M` is positive, and since the corner is FS,
  it suffices to compare `φ` and `ψ` on the projections of the corner, which are exactly the
  projections `q ≤ p` of `M`. -/
  let ι : hp.Corner →ₚ[ℂ] M := .ofClass (Corner.coeNonUnitalStarAlgHom ℂ hp)
  refine PositiveLinearMap.le_of_le_on_isStarProjection (φ.comp ι) (ψ.comp ι) (fun q hq ↦ ?_)
    (x := hp.toCorner ℂ a) (by simpa using hp.toCorner_mono ℂ ha)
  change φ (q : M) ≤ ψ (q : M)
  by_cases hq0 : (q : M) = 0
  · simp [hq0]
  · exact (h q (by simpa) hq0 (Corner.coe_le_of_isStarProjection hq)).le

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
  obtain ⟨p₁, hp₁, hp₁0, hp₁le, hall⟩ := exists_forall_lt (P := P)
    (scottContinuous_of_continuous (P := P) ψ hψc).scottContinuousOn hp₀.one_sub hlt
  /- With `ψ' := ψ (p₁ * · * p₁)`, which is ultraweakly continuous, we have
  `‖φ (x * p₁)‖ ^ 2 ≤ ‖φ 1‖ * ‖φ (p₁ * (star x * x) * p₁)‖ ≤ ‖φ 1‖ * ‖ψ' (star x * x)‖`,
  so `x ↦ φ (x * p₁)` is ultraweakly continuous. -/
  let ψ' : M →ₚ[ℂ] ℂ := ψ.comp (StarOrderedRing.conjPositiveLinearMap ℂ p₁)
  have hψ'c : Continuous fun x : σ(M, P) ↦ ψ' (ofUltraweak x) :=
    hψc.comp ((continuous_mul_const (toUltraweak ℂ P (star p₁))).comp
      (continuous_const_mul (toUltraweak ℂ P p₁)))
  let ω : StrongDual ℂ M := φ.toContinuousLinearMap ∘L (ContinuousLinearMap.mul ℂ M).flip p₁
  have hωc := continuous_of_norm_sq_le (P := P) ψ' hψ'c ω ‖φ 1‖ fun x ↦ by
    have hx := star_mul_self_nonneg x
    calc ‖ω x‖ ^ 2 ≤ ‖φ 1‖ * ‖φ (p₁ * (star x * x) * p₁)‖ := by
          simpa [ω, mul_assoc, hp₁.isSelfAdjoint.star_eq] using
            PositiveLinearMap.norm_map_star_mul_sq_le φ 1 (x * p₁)
      _ ≤ ‖φ 1‖ * ‖ψ' (star x * x)‖ := by
          gcongr
          simpa [ψ', hp₁.isSelfAdjoint.star_eq] using
            CStarAlgebra.norm_le_norm_of_le_of_nonneg (map_le_map_of_forall_lt (P := P) hp₁ hall hx)
              (map_nonneg φ (hp₁.isSelfAdjoint.conjugate_nonneg hx))
  /- Hence `x ↦ φ (x * (p₀ + p₁))` is ultraweakly continuous, contradicting maximality. -/
  have horth : p₁ ⋆⟂ p₀ := hp₀.one_sub_isStarOrtho.of_le hp₁.nonneg hp₁le
  have hcont : Continuous fun x : σ(M, P) ↦ φ (ofUltraweak x * (p₀ + p₁)) :=
    (hc₀.add hωc).congr fun x ↦ by simp [mul_add, ω]
  have := hmax ⟨horth.symm.isStarProjection_add hp₀ hp₁, hcont⟩ (le_add_of_nonneg_right hp₁.nonneg)
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
