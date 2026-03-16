import LeanOA.Mathlib.Algebra.Order.Star.Basic
import LeanOA.Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

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

open scoped ComplexStarModule in
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
