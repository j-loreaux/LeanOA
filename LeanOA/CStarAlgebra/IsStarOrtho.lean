module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import LeanOA.CStarAlgebra.ProperStar

open scoped Function StarRing
open Finset

public section

/-- Two elements `p` and `q` in a ⋆-ring are _star-orthogonal_ if `star q * p = 0`
and `p * star q = 0`. If `p` and `q` are both selfadjoint, this reduces to `p * q = 0`. -/
@[mk_iff]
structure IsStarOrtho {R : Type*} [NonUnitalSemiring R] [StarRing R] (p q : R) : Prop where
  mul_star_eq_zero : p * star q = 0
  star_mul_eq_zero : star q * p = 0

@[inherit_doc]
scoped[StarRing] infix:50 " ⋆⟂ " => IsStarOrtho

section NonUnitalSemiring

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] {p q : R}

lemma isStarOrtho_comm : p ⋆⟂ q ↔ q ⋆⟂ p := by
  simp_rw [isStarOrtho_iff]
  congr! 1
  · simp [← star_eq_zero (x := p * star q)]
  · simp [← star_eq_zero (x := star q * p)]

alias ⟨IsStarOrtho.symm, _⟩ := isStarOrtho_comm

instance : Std.Symm (· ⋆⟂ · : R → R → Prop) where
  symm _ _ := .symm

lemma isStarOrtho_iff' : p ⋆⟂ q ↔ p * star q = 0 ∧ star p * q = 0 := by
  rw [isStarOrtho_iff]
  simp [← star_eq_zero (x := star p * q)]

lemma IsStarOrtho.commute (h : p ⋆⟂ q) : Commute p (star q) :=
  h.mul_star_eq_zero.trans h.star_mul_eq_zero.symm

namespace IsStarOrtho

/-- The equation `IsStarOrtho.mul_star_eq_zero` with the roles of `p` and `q` interchanged. -/
lemma mul_star_eq_zero' (h : p ⋆⟂ q) : q * star p = 0 :=
  h.symm.mul_star_eq_zero

/-- The equation `IsStarOrtho.star_mul_eq_zero` with the roles of `p` and `q` interchanged. -/
lemma star_mul_eq_zero' (h : p ⋆⟂ q) : star p * q = 0 :=
  h.symm.star_mul_eq_zero

@[simp]
lemma zero_left (q : R) : (0 : R) ⋆⟂ q := by simp [isStarOrtho_iff]

@[simp]
lemma zero_right (p : R) : p ⋆⟂ 0 := by simp [isStarOrtho_iff]

protected lemma star (h : p ⋆⟂ q) : star p ⋆⟂ star q :=
  ⟨by rw [star_star, h.star_mul_eq_zero'], by rw [star_star, h.mul_star_eq_zero']⟩

@[simp]
lemma star_iff : star p ⋆⟂ star q ↔ p ⋆⟂ q :=
  ⟨fun h ↦ by simpa using h.star, .star⟩

lemma add_left {p₁ p₂ : R} (h₁ : p₁ ⋆⟂ q) (h₂ : p₂ ⋆⟂ q) : (p₁ + p₂) ⋆⟂ q :=
  ⟨by rw [add_mul, h₁.mul_star_eq_zero, h₂.mul_star_eq_zero, add_zero],
    by rw [mul_add, h₁.star_mul_eq_zero, h₂.star_mul_eq_zero, add_zero]⟩

lemma add_right {q₁ q₂ : R} (h₁ : p ⋆⟂ q₁) (h₂ : p ⋆⟂ q₂) : p ⋆⟂ (q₁ + q₂) :=
  (h₁.symm.add_left h₂.symm).symm

lemma smul_left {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] [SMulCommClass S R R]
    (h : p ⋆⟂ q) (c : S) : (c • p) ⋆⟂ q :=
  ⟨by rw [smul_mul_assoc, h.mul_star_eq_zero, smul_zero],
    by rw [mul_smul_comm, h.star_mul_eq_zero, smul_zero]⟩

lemma smul_right {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] [SMulCommClass S R R]
    (h : p ⋆⟂ q) (c : S) : p ⋆⟂ (c • q) :=
  (h.symm.smul_left c).symm

lemma sum_left {ι : Type*} {s : Finset ι} {f : ι → R} (h : ∀ i ∈ s, f i ⋆⟂ q) :
    (∑ i ∈ s, f i) ⋆⟂ q where
  mul_star_eq_zero := by rw [sum_mul]; exact sum_eq_zero fun i hi ↦ (h i hi).mul_star_eq_zero
  star_mul_eq_zero := by rw [mul_sum]; exact sum_eq_zero fun i hi ↦ (h i hi).star_mul_eq_zero

lemma sum_right {ι : Type*} {s : Finset ι} {f : ι → R} (h : ∀ i ∈ s, p ⋆⟂ f i) :
    p ⋆⟂ (∑ i ∈ s, f i) :=
  (sum_left fun i hi ↦ (h i hi).symm).symm

/-- If `p` and `q` are star-orthogonal, then so are `p * a * star p` and `q * b * star q`. -/
protected lemma star_right_conjugate (h : p ⋆⟂ q) (a b : R) :
    (p * a * star p) ⋆⟂ (q * b * star q) where
  mul_star_eq_zero := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star p) q, h.star_mul_eq_zero']
    simp
  star_mul_eq_zero := by
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc (star q) p, h.star_mul_eq_zero]
    simp

/-- If `p` and `q` are star-orthogonal, then so are `star p * a * p` and `star q * b * q`. -/
protected lemma star_left_conjugate (h : p ⋆⟂ q) (a b : R) :
    (star p * a * p) ⋆⟂ (star q * b * q) := by
  simpa using h.star.star_right_conjugate a b

attribute [local grind =] mul_assoc

/-- A version of `IsStarOrtho.mul_mul` with slightly weaker hypotheses. -/
lemma mul_mul' {p₁ p₂ q₁ q₂ : R} (h₁ : star q₁ * p₁ = 0) (h₂ : p₂ * star q₂ = 0) (a b : R) :
    (p₁ * a * p₂) ⋆⟂ (q₁ * b * q₂) where
  mul_star_eq_zero := by
    have : p₁ * a * p₂ * (star q₂ * (star b * star q₁)) =
        p₁ * a * (p₂ * star q₂) * star b * star q₁ := by simp [mul_assoc]
    simp [this, h₂]
  star_mul_eq_zero := by
    have : (star q₂ * (star b * star q₁)) * (p₁ * a * p₂) =
        star q₂ * star b * (star q₁ * p₁) * a * p₂ := by simp [mul_assoc]
    simp [this, h₁]

lemma mul_mul {p₁ p₂ q₁ q₂ : R} (h₁ : p₁ ⋆⟂ q₁) (h₂ : p₂ ⋆⟂ q₂) (a b : R) :
    (p₁ * a * p₂) ⋆⟂ (q₁ * b * q₂) :=
  mul_mul' h₁.star_mul_eq_zero h₂.mul_star_eq_zero a b

lemma mul_star_self (h : p ⋆⟂ q) : (p * star p) ⋆⟂ (q * star q) where
  mul_star_eq_zero := by simp [mul_assoc, ← mul_assoc (star p) q, h.star_mul_eq_zero']
  star_mul_eq_zero := by simp [mul_assoc, ← mul_assoc (star q) p, h.star_mul_eq_zero]

lemma star_mul_self (h : p ⋆⟂ q) : (star p * p) ⋆⟂ (star q * q) := by
  simpa using h.star.mul_star_self

lemma map {S F : Type*} [NonUnitalSemiring S] [StarRing S] [FunLike F R S]
    [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) (h : p ⋆⟂ q) : f p ⋆⟂ f q where
  mul_star_eq_zero := by rw [← map_star, ← map_mul, h.mul_star_eq_zero, map_zero]
  star_mul_eq_zero := by rw [← map_star, ← map_mul, h.star_mul_eq_zero, map_zero]

lemma star_add_mul_add (h : p ⋆⟂ q) :
    star (p + q) * (p + q) = star p * p + star q * q := by
  simp [mul_add, add_mul, h.star_mul_eq_zero', h.star_mul_eq_zero]

lemma add_mul_star_add (h : p ⋆⟂ q) :
    (p + q) * star (p + q) = p * star p + q * star q := by
  simpa using h.star.star_add_mul_add

end IsStarOrtho

lemma Set.Pairwise.star_sum_mul_sum_of_isStarOrtho {ι : Type*} {s : Finset ι} {f : ι → R}
    (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    star (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, star (f i) * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha' : f a ⋆⟂ ∑ i ∈ s, f i :=
      .sum_right fun j hj ↦ h (by simp) (by simp [hj]) (fun h' ↦ ha (h' ▸ hj))
    rw [sum_insert ha, sum_insert ha, ha'.star_add_mul_add, ih (h.mono (by simp))]

lemma Set.Pairwise.sum_mul_star_sum_of_isStarOrtho {ι : Type*} {s : Finset ι} {f : ι → R}
    (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    (∑ i ∈ s, f i) * star (∑ i ∈ s, f i) = ∑ i ∈ s, f i * star (f i) := by
  simpa using h.imp (fun _ _ ↦ IsStarOrtho.star) |>.star_sum_mul_sum_of_isStarOrtho

protected lemma IsSelfAdjoint.isStarOrtho_iff (hq : IsSelfAdjoint q) :
    p ⋆⟂ q ↔ p * q = 0 ∧ q * p = 0 := by
  rw [isStarOrtho_iff, hq.star_eq]

protected lemma IsSelfAdjoint.isStarOrtho_iff' (hp : IsSelfAdjoint p) :
    p ⋆⟂ q ↔ p * q = 0 ∧ q * p = 0 := by
  rw [isStarOrtho_comm, hp.isStarOrtho_iff, and_comm]

/-- Selfadjoint elements are star-orthogonal if and only if their product is zero. -/
@[grind =]
lemma isStarOrtho_iff_mul_eq_zero (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    p ⋆⟂ q ↔ p * q = 0 := by
  rw [hq.isStarOrtho_iff, and_iff_left_iff_imp]
  intro h
  simpa [hp.star_eq, hq.star_eq] using congr(star $h)

lemma IsStarOrtho.mul_eq_zero (h : p ⋆⟂ q) (hq : IsSelfAdjoint q) : p * q = 0 :=
  hq.isStarOrtho_iff.mp h |>.left

lemma IsStarOrtho.mul_eq_zero' (h : p ⋆⟂ q) (hq : IsSelfAdjoint q) : q * p = 0 :=
  hq.isStarOrtho_iff.mp h |>.right

/-- The sum of star-orthogonal star projections is a star projection. -/
lemma IsStarOrtho.isStarProjection_add (h : p ⋆⟂ q) (hp : IsStarProjection p)
    (hq : IsStarProjection q) : IsStarProjection (p + q) :=
  hp.add hq <| h.mul_eq_zero hq.isSelfAdjoint

/-- The sum of star projections is a star projection if and only if they are star-orthogonal. -/
lemma IsStarProjection.add_iff_isStarOrtho [IsCancelAdd R] [IsAddTorsionFree R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q) ↔ p ⋆⟂ q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.isStarProjection_add hp hq⟩
  have := hp.isIdempotentElem.add_iff hq.isIdempotentElem |>.mp h.isIdempotentElem
  grind [IsIdempotentElem.mul_eq_zero_of_anticommute]

/-- A finite sum of pairwise star-orthogonal star projections is a star projection.
The converse holds in a star-ordered ring with proper star. See `isStarProjection_sum_iff`.
The converse is not an immediate corollary of `IsStarProjection.add_iff_isStarOrtho` because we are
not assuming the intermediate sums (i.e., over a subset of `s`) are star projections. -/
lemma isStarProjection_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hf : ∀ i ∈ s, IsStarProjection (f i)) (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    IsStarProjection (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine IsStarOrtho.isStarProjection_add ?_ (hf a (by simp)) ?_
    · exact .sum_right fun j hj ↦ h (by simp) (by simp [hj]) (fun h' ↦ ha (h' ▸ hj))
    · exact ih (fun i hi ↦ hf i (by simp [hi])) <| h.mono <| by simp

end NonUnitalSemiring

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R] [StarRing R] {p q : R}

namespace IsStarOrtho

@[simp]
lemma neg_left_iff : (-p) ⋆⟂ q ↔ p ⋆⟂ q := by
  simp [isStarOrtho_iff]

@[simp]
lemma neg_right_iff : p ⋆⟂ (-q) ↔ p ⋆⟂ q := by
  simp [isStarOrtho_iff]

alias ⟨of_neg_left, neg_left⟩ := neg_left_iff
alias ⟨of_neg_right, neg_right⟩ := neg_right_iff

lemma sub_left {p₁ p₂ : R} (h₁ : p₁ ⋆⟂ q) (h₂ : p₂ ⋆⟂ q) : (p₁ - p₂) ⋆⟂ q := by
  simpa [sub_eq_add_neg] using h₁.add_left h₂.neg_left

lemma sub_right {q₁ q₂ : R} (h₁ : p ⋆⟂ q₁) (h₂ : p ⋆⟂ q₂) : p ⋆⟂ (q₁ - q₂) :=
  (h₁.symm.sub_left h₂.symm).symm

end IsStarOrtho

end NonUnitalRing

section Semiring

variable {R : Type*} [Semiring R] [StarRing R] {p q : R}

@[simp]
lemma isStarOrtho_one_left : 1 ⋆⟂ q ↔ q = 0 := by
  simp [isStarOrtho_iff]

@[simp]
lemma isStarOrtho_one_right : p ⋆⟂ 1 ↔ p = 0 := by
  simp [isStarOrtho_iff]

namespace IsStarOrtho

-- TODO: add `PNat` version
lemma pow_left (h : p ⋆⟂ q) {n : ℕ} (hn : n ≠ 0) : p ^ n ⋆⟂ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ⟨by rw [pow_succ, mul_assoc, h.mul_star_eq_zero, mul_zero],
    by rw [pow_succ', ← mul_assoc, h.star_mul_eq_zero, zero_mul]⟩

-- TODO: add `PNat` version
lemma pow_right (h : p ⋆⟂ q) {n : ℕ} (hn : n ≠ 0) : p ⋆⟂ q ^ n :=
  (h.symm.pow_left hn).symm

lemma pow_pow (h : p ⋆⟂ q) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : p ^ m ⋆⟂ q ^ n :=
  (h.pow_left hm).pow_right hn

end IsStarOrtho

end Semiring

section Ring

variable {R : Type*} [Ring R] [StarRing R] {p : R}

lemma IsStarProjection.isStarOrtho_one_sub (hp : IsStarProjection p) : p ⋆⟂ (1 - p) :=
  (isStarOrtho_iff_mul_eq_zero hp.isSelfAdjoint hp.one_sub.isSelfAdjoint).mpr
    hp.mul_one_sub_self

lemma IsStarProjection.one_sub_isStarOrtho (hp : IsStarProjection p) : (1 - p) ⋆⟂ p :=
  hp.isStarOrtho_one_sub.symm

end Ring

lemma max_pow_of_nonneg {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀] [PosMulMono M₀]
    [MulPosMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    max a b ^ n = max (a ^ n) (b ^ n) := by
  obtain (h | h) := le_total a b
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h n)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h n)]

lemma min_pow_of_nonneg {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀] [PosMulMono M₀]
    [MulPosMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    min a b ^ n = min (a ^ n) (b ^ n) := by
  obtain (h | h) := le_total a b
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ ha h n)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ hb h n)]

section IsProperStar

variable {A : Type*}

@[simp]
lemma isStarOrtho_self_iff [NonUnitalSemiring A] [StarRing A] [IsProperStar A]
    (p : A) : p ⋆⟂ p ↔ p = 0 := by
  simp [isStarOrtho_iff]

section StarOrderedRing

variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `0 ≤ a` and `c * a * star c = 0`, then `a * star c = 0`. -/
lemma mul_star_eq_zero_of_mul_mul_star_eq_zero {a c : A} (ha : 0 ≤ a)
    (h : c * a * star c = 0) : a * star c = 0 := by
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    have : star (x * star c) * (x * star c) = 0 := by simpa [mul_assoc] using h
    rw [mul_assoc, star_mul_self_eq_zero.mp this, mul_zero]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [← StarOrderedRing.nonneg_iff] at hx hy
    rw [mul_add, add_mul, add_eq_zero_iff_of_nonneg (star_right_conjugate_nonneg hx c)
      (star_right_conjugate_nonneg hy c)] at h
    rw [add_mul, ihx h.1, ihy h.2, add_zero]

lemma isStarOrtho_of_nonneg_iff {a b : A} (ha : 0 ≤ a) :
    a ⋆⟂ b ↔ star b * a * b = 0 ∧ b * a * star b = 0 := by
  rw [isStarOrtho_iff', (IsSelfAdjoint.of_nonneg ha).star_eq]
  refine ⟨fun h ↦ ⟨by simp [mul_assoc, h.2], by simp [mul_assoc, h.1]⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · exact mul_star_eq_zero_of_mul_mul_star_eq_zero ha h.2
  · simpa using mul_star_eq_zero_of_mul_mul_star_eq_zero ha (c := star b) (by simpa using h.1)

lemma isStarOrtho_of_nonneg_of_isSelfAdjoint_iff {a b : A} (ha : 0 ≤ a) (hb : IsSelfAdjoint b) :
    a ⋆⟂ b ↔ b * a * b = 0 := by
  simp [isStarOrtho_of_nonneg_iff ha, hb.star_eq]

namespace IsStarOrtho

lemma of_nonneg {a b : A} (ha : 0 ≤ a) (h₁ : star b * a * b ≤ 0) (h₂ : b * a * star b ≤ 0) :
    a ⋆⟂ b :=
  isStarOrtho_of_nonneg_iff ha |>.mpr
    ⟨le_antisymm h₁ (star_left_conjugate_nonneg ha b),
      le_antisymm h₂ (star_right_conjugate_nonneg ha b)⟩

lemma of_le {a b c : A} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ⋆⟂ c) : a ⋆⟂ c := by
  obtain ⟨h₁, h₂⟩ := isStarOrtho_of_nonneg_iff (ha.trans hab) |>.mp hbc
  exact .of_nonneg ha (h₁ ▸ star_left_conjugate_le_conjugate hab c)
    (h₂ ▸ star_right_conjugate_le_conjugate hab c)

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `a ⋆⟂ c`. -/
lemma of_add_left {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : a ⋆⟂ c :=
  h.of_le ha (le_add_of_nonneg_right hb)

/-- If `0 ≤ a` and `0 ≤ b` and `(a + b) ⋆⟂ c`, then `b ⋆⟂ c`. -/
lemma of_add_right {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a + b) ⋆⟂ c) : b ⋆⟂ c :=
  h.of_le hb (le_add_of_nonneg_left ha)

lemma add_iff {a b c : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ⋆⟂ c ↔ a ⋆⟂ c ∧ b ⋆⟂ c :=
  ⟨fun h ↦ ⟨h.of_add_left ha hb, h.of_add_right ha hb⟩, fun h ↦ h.1.add_left h.2⟩

lemma sum_iff {ι : Type*} {s : Finset ι} {f : ι → A} {c : A} (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ⋆⟂ c ↔ ∀ j ∈ s, f j ⋆⟂ c :=
  ⟨fun h _j hj ↦ h.of_le (hf _ hj) (Finset.single_le_sum hf hj), sum_left⟩

/-- If each `f i` is nonnegative and `(∑ i ∈ s, f i) ⋆⟂ c`, then `f j ⋆⟂ c` for every `j ∈ s`. -/
alias ⟨of_sum, _⟩ := sum_iff

end IsStarOrtho

end StarOrderedRing

/-- If `p` and `p + q` are star projections and `0 ≤ q`, then `q ⋆⟂ p`. -/
private lemma IsStarProjection.isStarOrtho_of_add [NonUnitalRing A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {p q : A} (hp : IsStarProjection p)
    (hq : 0 ≤ q) (hr : IsStarProjection (p + q)) : q ⋆⟂ p := by
  set r := p + q
  have hpp : p * p = p := hp.isIdempotentElem.eq
  /- `p * q * p = p * r * p - p`, and `p - p * r * p = (p - p * r) * star (p - p * r) ≥ 0`. -/
  have h₁ : p * q * p = p * r * p - p := by
    simp [r, mul_add, add_mul, hpp]
  have h₂ : p - p * r * p = (p - p * r) * star (p - p * r) := by
    have hrr : p * r * r * p = p * r * p := by rw [mul_assoc p r r, hr.isIdempotentElem.eq]
    rw [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq]
    simp only [mul_sub, sub_mul, ← mul_assoc, hpp, hrr]
    abel
  have h : p * q * p ≤ 0 := by
    rw [h₁, sub_nonpos, ← sub_nonneg, h₂]
    exact mul_star_self_nonneg _
  exact .of_nonneg hq (by rwa [hp.isSelfAdjoint.star_eq]) (by rwa [hp.isSelfAdjoint.star_eq])

/-- In a star-ordered ring with proper star (e.g., a C⋆-algebra), a finite sum of star
projections is a star projection if and only if they are pairwise star-orthogonal. -/
lemma isStarProjection_sum_iff [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [IsProperStar A] {ι : Type*} {s : Finset ι} {f : ι → A}
    (hf : ∀ i ∈ s, IsStarProjection (f i)) :
    IsStarProjection (∑ i ∈ s, f i) ↔ (s : Set ι).Pairwise (( · ⋆⟂  ·) on f) := by
  classical
  refine ⟨fun hP i hi j hj hij ↦ ?_, isStarProjection_sum hf⟩
  rw [← Finset.add_sum_erase s f hi] at hP
  have hf' (k : ι) (hk : k ∈ s.erase i) : 0 ≤ f k := (hf k (by grind)).nonneg
  exact (hf i hi).isStarOrtho_of_add (Finset.sum_nonneg hf') hP |>.of_sum hf' j
    (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩) |>.symm

/-- If `a` is normal and `a ⋆⟂ b`, then `star a ⋆⟂ b`. -/
lemma IsStarOrtho.star_left_of_isStarNormal [NonUnitalSemiring A] [StarRing A] [IsProperStar A]
    {a b : A} (h : a ⋆⟂ b) (ha : IsStarNormal a) : star a ⋆⟂ b where
  mul_star_eq_zero := by
    rw [← star_mul_self_eq_zero]
    simp only [star_mul, star_star, mul_assoc]
    rw [← mul_assoc a, ← ha.star_comm_self.eq, mul_assoc, h.mul_star_eq_zero, mul_zero, mul_zero]
  star_mul_eq_zero := by
    rw [← mul_star_self_eq_zero]
    simp only [star_mul, star_star, ← mul_assoc]
    rw [mul_assoc _ (star a), ha.star_comm_self.eq, ← mul_assoc, h.star_mul_eq_zero, zero_mul,
      zero_mul]

end IsProperStar

section CFC

variable {A : Type*} [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [IsSemitopologicalRing A] [T2Space A] {a b : A}

attribute [simp] cfcₙHom_id cfcHom_id

namespace IsStarOrtho

section Complex

variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [IsProperStar A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- If `a` is normal and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_complex_left (f : ℂ → ℂ) (h : a ⋆⟂ b) (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℂ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  have := isCompact_iff_compactSpace.mp <|
    NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℂ) (p := IsStarNormal) a
  have h' := h.star_left_of_isStarNormal ha
  rw [cfcₙ_apply f a]
  constructor
  · refine ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero _ _
      (by simpa using h.mul_star_eq_zero) ?_ (cfcₙHom_continuous ha) _
    simpa [map_star] using h'.mul_star_eq_zero
  · refine ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero _ _
      (by simpa using h.star_mul_eq_zero) ?_ (cfcₙHom_continuous ha) _
    simpa [map_star] using h'.star_mul_eq_zero

/-- If `b` is normal and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_complex_right (f : ℂ → ℂ) (h : a ⋆⟂ b) (hb : IsStarNormal b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℂ b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_complex_left f).symm

end Complex

section Real

variable [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `a` is selfadjoint and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_real_left (f : ℝ → ℝ) (h : a ⋆⟂ b) (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  have := isCompact_iff_compactSpace.mp <|
    NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ) (p := IsSelfAdjoint) a
  rw [cfcₙ_apply f a]
  constructor
  · refine ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero _ _ ?_ ?_
      (cfcₙHom_continuous ha) _
    all_goals simpa [map_star, cfcₙHom_id ha, ha.star_eq] using h.mul_star_eq_zero
  · refine ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero _ _ ?_ ?_
      (cfcₙHom_continuous ha) _
    all_goals simpa [map_star, cfcₙHom_id ha, ha.star_eq] using h.star_mul_eq_zero

/-- If `b` is selfadjoint and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_real_right (f : ℝ → ℝ) (h : a ⋆⟂ b) (hb : IsSelfAdjoint b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_real_left f).symm

variable [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

open scoped NNReal in
/-- If `a` is nonnegative and `a ⋆⟂ b`, then `cfcₙ f a ⋆⟂ b`. -/
lemma cfcₙ_nnreal_left (f : ℝ≥0 → ℝ≥0) (h : a ⋆⟂ b) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ⋆⟂ b := by
  rw [cfcₙ_nnreal_eq_real f a]
  refine h.cfcₙ_real_left _ (.of_nonneg ha) ?_ (by simpa)
  refine NNReal.continuous_coe.comp_continuousOn <|
    hf.comp continuous_real_toNNReal.continuousOn fun x hx ↦ ?_
  rw [← (QuasispectrumRestricts.nnreal_of_nonneg ha).algebraMap_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa

open scoped NNReal in
/-- If `b` is nonnegative and `a ⋆⟂ b`, then `a ⋆⟂ cfcₙ f b`. -/
lemma cfcₙ_nnreal_right (f : ℝ≥0 → ℝ≥0) (h : a ⋆⟂ b) (hb : 0 ≤ b := by cfc_tac)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 b) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    a ⋆⟂ cfcₙ f b :=
  (h.symm.cfcₙ_nnreal_left f).symm

open CFC

lemma _root_.isStarOrtho_sqrt_right_iff {a b : A} (ha : 0 ≤ a) : b ⋆⟂ sqrt a ↔ b ⋆⟂ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.cfcₙ_nnreal_right _⟩
  have := h.cfcₙ_nnreal_right (fun x ↦ x * x)
  rwa [cfcₙ_mul .., cfcₙ_id' .., sqrt_mul_sqrt_self _] at this

lemma _root_.isStarOrtho_sqrt_left_iff {a b : A} (ha : 0 ≤ a) : sqrt a ⋆⟂ b ↔ a ⋆⟂ b := by
  simpa [isStarOrtho_comm] using isStarOrtho_sqrt_right_iff ha

alias ⟨of_sqrt_right, sqrt_right⟩ := isStarOrtho_sqrt_right_iff
alias ⟨of_sqrt_left, sqrt_left⟩ := isStarOrtho_sqrt_left_iff

end Real

end IsStarOrtho

end CFC

section CStarRing

variable {A : Type*} [NonUnitalCStarAlgebra A] {a b : A}

namespace IsStarOrtho

lemma norm_add (h : a ⋆⟂ b) : ‖a + b‖ = max ‖a‖ ‖b‖ := by
  rw [← sq_eq_sq₀ ?h₁ ?h₂, max_pow_of_nonneg ?h₃ ?h₄]
  case h₁ | h₂ | h₃ | h₄ => positivity
  simp_rw [sq, ← CStarRing.norm_star_mul_self, h.star_add_mul_add]
  refine IsSelfAdjoint.norm_add_eq_max (by aesop) (by aesop) ?_
  simpa using h.star_mul_self.mul_star_eq_zero

lemma nnnorm_add (h : a ⋆⟂ b) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  Subtype.ext <| h.norm_add

lemma norm_sub (h : a ⋆⟂ b) : ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using h.neg_right.norm_add

lemma nnnorm_sub (h : a ⋆⟂ b) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
  Subtype.ext <| h.norm_sub

lemma nnnorm_sum {ι : Type*} {s : Finset ι} {f : ι → A}
    (h : (s : Set ι).Pairwise ((· ⋆⟂ ·) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup fun (x : ι) => ‖f x‖₊ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.coe_insert, Set.pairwise_insert_of_symm, SetLike.mem_coe, ne_eq] at h
    suffices f j ⋆⟂ ∑ i ∈ s, f i by
      simp_all [this.nnnorm_add, ih h.1]
    exact .sum_right fun i hi ↦ h.2 i hi (by grind)

end IsStarOrtho

end CStarRing
