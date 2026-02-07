import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace
import LeanOA.ComplexOrder
import Mathlib.Algebra.Group.PNatPowAssoc

namespace PositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂]

@[simp]
lemma coe_toLinearMap (f : E₁ →ₚ[R] E₂) : (f.toLinearMap : E₁ → E₂) = f :=
  rfl

lemma toLinearMap_injective : Function.Injective (toLinearMap : (E₁ →ₚ[R] E₂) → (E₁ →ₗ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

instance : Zero (E₁ →ₚ[R] E₂) where
  zero := .mk (0 : E₁ →ₗ[R] E₂) fun _ ↦ by simp

@[simp]
lemma toLinearMap_zero : (0 : E₁ →ₚ[R] E₂).toLinearMap = 0 :=
  rfl

@[simp]
lemma zero_apply (x : E₁) : (0 : E₁ →ₚ[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂]

instance : Add (E₁ →ₚ[R] E₂) where
  add f g := .mk (f.toLinearMap + g.toLinearMap) fun _ _ h ↦
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]
lemma toLinearMap_add (f g : E₁ →ₚ[R] E₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := by
  rfl

@[simp]
lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

instance : SMul ℕ (E₁ →ₚ[R] E₂) where
  smul n f := .mk (n • f.toLinearMap) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]
lemma toLinearMap_nsmul (f : E₁ →ₚ[R] E₂) (n : ℕ) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

@[simp]
lemma nsmul_apply (f : E₁ →ₚ[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

instance : AddCommMonoid (E₁ →ₚ[R] E₂) :=
  toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

end PositiveLinearMap

namespace ContinuousPositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂]
    [TopologicalSpace E₁] [TopologicalSpace E₂]

@[simp]
lemma coe_toPositiveLinearMap (f : E₁ →P[R] E₂) :
    (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl

@[simp]
lemma coe_toContinuousLinearMap (f : E₁ →P[R] E₂) :
    (f.toContinuousLinearMap : E₁ → E₂) = f :=
  rfl

lemma toPositiveLinearMap_injective :
    Function.Injective (fun f ↦ f.toPositiveLinearMap : (E₁ →P[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

lemma toContinuousLinearMap_injective :
    Function.Injective (fun f ↦ f.toContinuousLinearMap : (E₁ →P[R] E₂) → (E₁ →L[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

instance : Zero (E₁ →P[R] E₂) where
  zero := .mk (0 : E₁ →ₚ[R] E₂) <| by fun_prop

@[simp]
lemma toPositiveLinearMap_zero : (0 : E₁ →P[R] E₂).toPositiveLinearMap = 0 :=
  rfl

@[simp]
lemma toContinuousLinearMap_zero : (0 : E₁ →P[R] E₂).toContinuousLinearMap = 0 :=
  rfl

@[simp]
lemma zero_apply (x : E₁) : (0 : E₁ →P[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂] [ContinuousAdd E₂]

instance : Add (E₁ →P[R] E₂) where
  add f g := .mk (f.toPositiveLinearMap + g.toPositiveLinearMap) <|
    show Continuous (fun x ↦ f x + g x) by fun_prop

@[simp]
lemma toPositiveLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toPositiveLinearMap = f.toPositiveLinearMap + g.toPositiveLinearMap := by
  rfl

@[simp]
lemma toContinuousLinearMap_add (f g : E₁ →P[R] E₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := by
  rfl

@[simp]
lemma add_apply (f g : E₁ →P[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

instance : SMul ℕ (E₁ →P[R] E₂) where
  smul n f := .mk (n • f.toPositiveLinearMap) <|
    show Continuous (fun x ↦ n • f x) by fun_prop

@[simp]
lemma toPositiveLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toPositiveLinearMap = n • f.toPositiveLinearMap :=
  rfl

@[simp]
lemma toContinuousLinearMap_nsmul (f : E₁ →P[R] E₂) (n : ℕ) :
    (n • f).toContinuousLinearMap = n • f.toContinuousLinearMap :=
  rfl

@[simp]
lemma nsmul_apply (f : E₁ →P[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

instance : AddCommMonoid (E₁ →P[R] E₂) :=
  toPositiveLinearMap_injective.addCommMonoid _ toPositiveLinearMap_zero toPositiveLinearMap_add
    toPositiveLinearMap_nsmul

end ContinuousPositiveLinearMap


section CFC

lemma CFC.mul_self_eq_zero_iff {R A : Type*} {p : A → Prop} [Semifield R] [Nontrivial R]
    [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a := by cfc_tac) :
    a * a = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp⟩
  refine CFC.eq_zero_of_quasispectrum_eq_zero (R := R) a fun r hr ↦ ?_
  rw [← cfcₙ_id' R a, ← cfcₙ_mul .., ← cfcₙ_zero (R := R) a, cfcₙ_eq_cfcₙ_iff_eqOn] at h
  simpa using h hr

lemma CFC.pow_eq_zero_iff {R A : Type} {p : A → Prop} [Semifield R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
    (a : A) (n : ℕ) (hn : n ≠ 0) (hp : p a := by cfc_tac) :
    a ^ n = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp [hn]⟩
  refine CFC.eq_zero_of_spectrum_subset_zero (R := R) a fun r hr ↦ ?_
  rw [← cfc_id' R a, ← cfc_pow .., ← cfc_zero (R := R) a, cfc_eq_cfc_iff_eqOn] at h
  simpa [hn] using h hr

open NonUnitalIsometricContinuousFunctionalCalculus in
lemma CFC.norm_mul_self {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A]
    [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p] (a : A) (ha : p a := by cfc_tac) :
    ‖a * a‖ = ‖a‖ ^ 2 := by
  apply le_antisymm (by simpa [sq] using norm_mul_le ..)
  have ⟨⟨x, hx, hx'⟩, h₂⟩ := isGreatest_norm_quasispectrum (𝕜 := 𝕜) a ha
  rw [← hx', ← norm_pow, sq, ← cfcₙ_id' 𝕜 a, ← cfcₙ_mul ..]
  exact norm_apply_le_norm_cfcₙ (fun x ↦ x * x) a hx

--- this is stupid. Can we please just have `Pow A ℕ+` for semigroups?
open NonUnitalIsometricContinuousFunctionalCalculus in
lemma CFC.norm_mul_mul_self {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A]
    [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p] (a : A) (ha : p a := by cfc_tac) :
    ‖a * a * a‖ = ‖a‖ ^ 3 := by
  apply le_antisymm (by simpa [pow_succ] using norm_mul₃_le ..)
  have ⟨⟨x, hx, hx'⟩, h₂⟩ := isGreatest_norm_quasispectrum (𝕜 := 𝕜) a ha
  rw [← hx', ← norm_pow, ← cfcₙ_id' 𝕜 a, ← cfcₙ_mul .., ← cfcₙ_mul ..]
  simpa only [pow_succ, pow_zero, one_mul] using norm_apply_le_norm_cfcₙ (fun x ↦ x * x * x) a hx

open IsometricContinuousFunctionalCalculus in
protected lemma CFC.norm_pow {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A]
    [StarRing A] [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    (a : A) (n : ℕ) (hn : n ≠ 0) (ha : p a := by cfc_tac) :
    ‖a ^ n‖ = ‖a‖ ^ n := by
  obtain (h | h) := subsingleton_or_nontrivial A
  · simp [h.elim a 0, hn]
  apply le_antisymm (by simpa using norm_pow_le' _ (Nat.zero_lt_of_ne_zero hn))
  have ⟨⟨x, hx, hx'⟩, h₂⟩ := isGreatest_norm_spectrum (𝕜 := 𝕜) a ha
  simp only at hx'
  rw [← hx', ← norm_pow, ← cfc_id' 𝕜 a, ← cfc_pow ..]
  exact norm_apply_le_norm_cfc (· ^ n) a hx

lemma IsSelfAdjoint.iff_of_le {R : Type*} [NonUnitalRing R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] {a b : R} (hab : a ≤ b) :
    IsSelfAdjoint a ↔ IsSelfAdjoint b := by
  replace hab := (sub_nonneg.mpr hab).isSelfAdjoint
  exact ⟨fun ha ↦ by simpa using hab.add ha, fun hb ↦ by simpa using (hab.sub hb).neg⟩

alias ⟨IsSelfAdjoint.of_ge, IsSelfAdjoint.of_le⟩ := IsSelfAdjoint.iff_of_le

theorem CStarAlgebra.norm_posPart_mono {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖a⁺‖ ≤ ‖b⁺‖ := by
  have hb : IsSelfAdjoint b := ha.of_ge hab
  replace h : a ≤ b⁺ := hab.trans CFC.le_posPart
  have key := IsSelfAdjoint.conjugate_le_conjugate h (CFC.posPart_nonneg a).isSelfAdjoint
  nth_rw 2 [← CFC.posPart_sub_negPart a] at key
  simp only [mul_sub, CFC.posPart_mul_negPart, sub_zero] at key
  obtain (ha' | ha') := eq_zero_or_norm_pos (a⁺)
  · simp [ha']
  suffices ‖a⁺‖ ^ 3 ≤ ‖a⁺‖ * ‖b⁺‖ * ‖a⁺‖ by simpa [pow_succ, ha']
  calc
    ‖a⁺‖ ^ 3 = ‖a⁺ * a⁺ * a⁺‖ := by rw [CFC.norm_mul_mul_self (𝕜 := ℝ) a⁺]
    _ ≤ ‖a⁺ * b⁺ * a⁺‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le (by cfc_tac) key
    _ ≤ ‖a⁺‖ * ‖b⁺‖ * ‖a⁺‖ := norm_mul₃_le ..

theorem CStarAlgebra.norm_posPart_anti {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖b⁻‖ ≤ ‖a⁻‖ := by
  have hb : IsSelfAdjoint b := by simpa using (sub_nonneg.mpr hab).isSelfAdjoint.add ha
  rw [← neg_neg a, ← neg_le] at hab
  simpa using CStarAlgebra.norm_posPart_mono hab hb.neg

theorem IsSelfAdjoint.norm_le_max_of_le_of_le {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b c : A} (ha : IsSelfAdjoint a := by cfc_tac)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ‖b‖ ≤ max ‖a‖ ‖c‖ := by
  have hb := ha.of_ge hab
  calc
    ‖b‖ = max ‖b⁻‖ ‖b⁺‖ := by simpa [max_comm] using hb.norm_eq_max_norm_posPart_negPart b
    _ ≤ max ‖a⁻‖ ‖c⁺‖ := max_le_max (CStarAlgebra.norm_posPart_anti hab ha)
      (CStarAlgebra.norm_posPart_mono hbc hb)
    _ ≤ max ‖a‖ ‖c‖ := max_le_max (by simp) (by simp)

end CFC

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] [CompleteSpace P]

namespace Ultraweak

open scoped ComplexOrder

variable (M P)

open PositiveContinuousLinearMap in
/-- Linear combinations of ultraweakly continuous positive linear functionals. -/
private def E : Submodule ℂ (StrongDual ℂ σ(M, P)) :=
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

open Filter in
lemma _root_.Cauchy.map_of_le {α β : Type*} [UniformSpace α] [UniformSpace β]
    {l : Filter α} {f : α → β} (hl : Cauchy l) {s : Set α}
    (hf : UniformContinuousOn f s) (hls : l ≤ 𝓟 s) :
    Cauchy (map f l) := by
  rw [uniformContinuousOn_iff_restrict] at hf
  have hl' : Cauchy (comap (Subtype.val : s → α) l) := by
    apply hl.comap' ?_ (comap_coe_neBot_of_le_principal (h := hl.1) hls)
    exact le_def.mpr fun x a ↦ a
  simpa [Set.restrict_def, ← Function.comp_def, ← map_map,
    subtype_coe_map_comap, inf_eq_left.mpr hls] using hl'.map hf

private lemma uniformContinuousOn_weakEEquiv_symm_comp_ofUltraweak (r : ℝ) :
    UniformContinuousOn ((weakEEquiv M P).symm ∘ ofUltraweak (𝕜 := ℂ) (P := P))
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r) := by
  rw [uniformContinuousOn_iff_restrict]
  exact uniformContinuous_subtype_val.comp (weakEUniformEquiv M P r).uniformContinuous

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

private lemma mapsTo_toUltraweak_comp_weakEEquiv_preimage_closedBall (r : ℝ) :
    Set.MapsTo (toUltraweak ℂ P ∘ weakEEquiv M P)
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r))
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r) :=
  fun x hx ↦ ((weakEUniformEquiv M P r).symm ⟨x, hx⟩).2

open Filter in
lemma cauchy_of_forall_posCLM_cauchy_map {l : Filter σ(M, P)} {r : ℝ}
    (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r))
    (hl : ∀ φ : σ(M, P) →P[ℂ] ℂ, Cauchy (Filter.map φ l)) :
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

lemma ComplexStarModule.ext_realPart_imaginaryPart {M : Type*}
    [AddCommGroup M] [StarAddMonoid M] [Module ℂ M] [StarModule ℂ M] {x y : M}
    (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) :
    x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x, ← realPart_add_I_smul_imaginaryPart y, h₁, h₂]

lemma ComplexStarModule.ext_iff_realPart_imaginaryPart {M : Type*}
    [AddCommGroup M] [StarAddMonoid M] [Module ℂ M] [StarModule ℂ M] {x y : M} :
    x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y :=
  ⟨by grind, fun h ↦ ext_realPart_imaginaryPart h.1 h.2⟩

lemma StarOrderedRing.nonneg_iff_realPart_imaginaryPart {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a : A} :
    0 ≤ a ↔ 0 ≤ ℜ a ∧ ℑ a = 0 := by
  constructor
  · refine fun h ↦ ⟨?_, h.isSelfAdjoint.imaginaryPart⟩
    have := h.isSelfAdjoint.coe_realPart ▸ h
    simpa
  · intro h
    rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using h.1

lemma StarOrderedRing.le_iff_realPart_imaginaryPart {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} :
    a ≤ b ↔ ℜ a ≤ ℜ b ∧ ℑ a = ℑ b := by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using
    nonneg_iff_realPart_imaginaryPart (a := b - a)

lemma StarOrderedRing.imaginaryPart_eq_of_le {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} (hab : a ≤ b) :
    ℑ a = ℑ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.2

lemma StarOrderedRing.realPart_mono {A : Type*}
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    [Module ℂ A] [StarModule ℂ A] {a b : A} (hab : a ≤ b) :
    ℜ a ≤ ℜ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.1

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
    rw [StarOrderedRing.imaginaryPart_eq_of_le (hb hx),
      StarOrderedRing.imaginaryPart_eq_of_le (hb hx₀)]
  simp only [Metric.mem_closedBall, dist_eq_norm]
  rw [← this.coe_realPart]
  simp only [map_sub, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
  apply IsSelfAdjoint.norm_le_max_of_le_of_le (by cfc_tac)
  all_goals simpa using StarOrderedRing.realPart_mono (by aesop)

lemma _root_.DirectedOn.inter {α : Type*} {r : α → α → Prop} {s : Set α}
    [IsTrans α r] (hs : DirectedOn r s) (x₀ : α) :
    DirectedOn r (s ∩ {x | r x₀ x}) := by
  rintro y ⟨hy, y₁⟩ z ⟨hz, h₂⟩
  obtain ⟨w, hw, hyw, hzw⟩ := hs y hy z hz
  exact ⟨w, ⟨hw, trans y₁ hyw⟩ , ⟨hyw, hzw⟩⟩

variable {M P} in
omit [CompleteSpace P] [StarOrderedRing M] in
lemma monotone_ofUltraweak : Monotone (ofUltraweak : σ(M, P) → M) := fun _ _ ↦ id
variable {M P} in
omit [CompleteSpace P] [StarOrderedRing M] in
lemma monotone_toUltraweak : Monotone (toUltraweak ℂ P : M → σ(M, P)) := fun _ _ ↦ id

open Filter Topology Set in
lemma DirectedOn.exists_isLUB (s : Set σ(M, P)) (hs : DirectedOn (· ≤ ·) s)
    (hnon : s.Nonempty) (hbd : BddAbove s) :
    ∃ x : σ(M, P), IsLUB s x ∧ Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 x) := by
  let ⟨x₀, hx₀⟩ := hnon
  have hbd' : BddAbove (ofUltraweak '' (s ∩ Ici x₀)) :=
    monotone_ofUltraweak.map_bddAbove hbd.inter_of_left
  have hbd'' : BddBelow (ofUltraweak '' (s ∩ Ici x₀)) := by
    use ofUltraweak x₀
    rintro - ⟨x, hx, rfl⟩
    aesop
  obtain ⟨r, hr⟩ := isBounded_of_bddAbove_of_bddBelow hbd' hbd'' |>.subset_closedBall 0
  have h_map_le : map (Subtype.val : s → σ(M, P)) atTop ≤
      𝓟 (ofUltraweak ⁻¹' Metric.closedBall 0 r) := by
    simp only [le_principal_iff, mem_map]
    refine mem_of_superset (Ici_mem_atTop (⟨x₀, hx₀⟩ : s)) ?_
    intro ⟨x, hx⟩ hxx₀
    simp only [mem_Ici, Subtype.mk_le_mk, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] at hxx₀ ⊢
    simpa using hr ⟨_, ⟨hx, hxx₀⟩, rfl⟩
  have : IsDirectedOrder s := ⟨hs.directed_val⟩
  have : Nonempty s := hnon.to_subtype
  have h_cauchy : Cauchy (map ((↑) : s → σ(M, P)) atTop) := by
    apply cauchy_of_forall_posCLM_cauchy_map M P h_map_le fun φ ↦ ?_
    have hφ := OrderHomClass.mono φ
    exact Tendsto.cauchy_map <| tendsto_atTop_ciSup' (hφ.comp (Subtype.mono_coe s)) <| by
      simpa [← Function.comp_def, Set.range_comp]
        using (OrderHomClass.mono φ |>.map_bddAbove hbd)
  obtain ⟨x, -, hx⟩ := isCompact_closedBall ℂ P (0 : M) r |>.isComplete _ h_cauchy h_map_le
  refine ⟨x, ?_, hx⟩
  simpa [setOf] using isLUB_of_tendsto_atTop' (β := s) (Subtype.mono_coe s) hx

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

open Filter in
instance : SupConvergenceClass σ(M, P) where
  tendsto_coe_atTop_isLUB a s hsa := by
    by_cases! h : (atTop : Filter s).NeBot
    · rw [atTop_neBot_iff] at h
      obtain ⟨h₁, h₂⟩ := h
      replace h₁ : s.Nonempty := Set.nonempty_coe_sort.mp h₁
      replace h₂ : DirectedOn (· ≤ ·) s := by
        rw [directedOn_iff_directed]
        obtain ⟨h₂⟩ := h₂
        exact h₂
      obtain ⟨u, hu₁, hu₂⟩ := DirectedOn.exists_isLUB M P s h₂ h₁ ⟨_, hsa.1⟩
      exact hsa.unique hu₁ ▸ hu₂
    · simp [h]

end Ultraweak
