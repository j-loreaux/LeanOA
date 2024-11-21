import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import LeanOA.ForMathlib.Topology.Algebra.NonUnitalStarAlgebra
import LeanOA.Notation
import LeanOA.TopologicalAlgebra

/-! # range of the continuous functional calculus

This file contains results about the range of the continuous functional calculus, and consequences thereof.
-/

open Topology

open scoped CStarAlgebra

namespace Set

lemma isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, setOf_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
  refine isClosed_imp (by simp) <| isClosed_eq ?_ ?_
  all_goals fun_prop

end Set

namespace StarAlgebra

open StarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [Algebra R A]
  [StarRing A] [StarModule R A] [TopologicalSpace A] [TopologicalSemiring A] [ContinuousStar A]
  [T2Space A]

lemma topologicalClosure_adjoin_le_centralizer_centralizer (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

lemma elemental.le_centralizer_centralizer (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer R {x}

end StarAlgebra

section CFCRangeCommute

variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [StarModule 𝕜 A] [ContinuousFunctionalCalculus 𝕜 p]

open StarAlgebra in
lemma ContinuousMap.elemental_eq_top (s : Set 𝕜) [CompactSpace s] :
    elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤ := by
  rw [StarAlgebra.elemental, ← polynomialFunctions.starClosure_topologicalClosure,
    polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

theorem cfc_range {a : A} (ha : p a) :
    Set.range (cfc (R := 𝕜) · a) = (cfcHom ha (R := 𝕜)).range := by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : ContinuousOn f (spectrum 𝕜 a)
    · simpa only [cfc_apply f a, SetLike.mem_coe] using ⟨_, rfl⟩
    · simpa only [cfc_apply_of_not_continuousOn a hf] using zero_mem _
  · rintro ⟨f, rfl⟩
    classical
    let f' (x : 𝕜) : 𝕜 := if hx : x ∈ spectrum 𝕜 a then f ⟨x, hx⟩ else 0
    have hff' : f = Set.restrict (spectrum 𝕜 a) f'  := by ext; simp [f']
    have : ContinuousOn f' (spectrum 𝕜 a) :=
      continuousOn_iff_continuous_restrict.mpr (hff' ▸ map_continuous f)
    use f'
    simp only [cfc_apply f' a]
    congr!
    exact hff'.symm

variable [TopologicalRing A] [ContinuousStar A]

open StarAlgebra

open scoped ContinuousFunctionalCalculus in
theorem cfcHom_range {a : A} (ha : p a) :
    (cfcHom ha (R := 𝕜)).range = elemental 𝕜 a := by
  rw [StarAlgHom.range_eq_map_top, ← ContinuousMap.elemental_eq_top, StarAlgebra.elemental,
    ← StarSubalgebra.topologicalClosure_map _ _ (cfcHom_isClosedEmbedding ha (R := 𝕜)),
    StarAlgHom.map_adjoin]
  congr
  simpa using cfcHom_id ha

variable {𝕜}

theorem cfcHom_apply_mem_elemental {a : A} (ha : p a) (f : C(spectrum 𝕜 a, 𝕜)) :
    cfcHom ha f ∈ elemental 𝕜 a :=
  cfcHom_range 𝕜 ha ▸ ⟨f, rfl⟩

variable [T2Space A]

open StarSubalgebra elemental in
theorem commute_cfcHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  have hb : b ∈ centralizer 𝕜 {a} := by simpa [mem_centralizer_iff] using ⟨hb₁.eq, hb₂.eq⟩
  le_centralizer_centralizer 𝕜 a (cfcHom_apply_mem_elemental ha f) b (.inl hb) |>.symm

protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  commute_cfcHom ha hb (ha'.star_eq.symm ▸ hb) f

theorem commute_cfc {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ commute_cfcHom ha hb₁ hb₂ ⟨_, hf.restrict⟩

protected theorem IsSelfAdjoint.commute_cfc {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  commute_cfc hb₁ (ha.star_eq.symm ▸ hb₁) f

end CFCRangeCommute

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [StarRing A] [StarModule R A] [TopologicalSpace A] [TopologicalSemiring A] [ContinuousStar A]
  [T2Space A] [ContinuousConstSMul R A]

lemma topologicalClosure_adjoin_le_centralizer_centralizer (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

lemma elemental.le_centralizer_centralizer (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer R {x}

end NonUnitalStarAlgebra

section NonUnital


variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A]
variable [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus 𝕜 p]

theorem cfcₙ_range {a : A} (ha : p a) :
    Set.range (cfcₙ (R := 𝕜) · a) = NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) := by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : ContinuousOn f (quasispectrum 𝕜 a) ∧ f 0 = 0
    · obtain ⟨hf, hf₀⟩ := hf
      simpa only [cfcₙ_apply f a, SetLike.mem_coe] using ⟨_, rfl⟩
    · obtain (hf | hf₀) := not_and_or.mp hf
      · simpa only [cfcₙ_apply_of_not_continuousOn a hf] using zero_mem _
      · simpa only [cfcₙ_apply_of_not_map_zero a hf₀] using zero_mem _
  · rintro ⟨f, rfl⟩
    classical
    let f' (x : 𝕜) : 𝕜 := if hx : x ∈ quasispectrum 𝕜 a then f ⟨x, hx⟩ else 0
    have hff' : f = Set.restrict (quasispectrum 𝕜 a) f'  := by ext; simp [f']
    have : ContinuousOn f' (quasispectrum 𝕜 a) :=
      continuousOn_iff_continuous_restrict.mpr (hff' ▸ map_continuous f)
    have hf'₀ : f' 0 = 0 := by simp only [quasispectrum.zero_mem, ↓reduceDIte, f']; exact map_zero f
    use f'
    simp only [cfcₙ_apply f' a]
    congr!
    exact hff'.symm

variable [ContinuousConstSMul 𝕜 A]
variable [StarModule 𝕜 A]
variable [TopologicalRing A] [ContinuousStar A]

open NonUnitalStarAlgebra

-- this can be added after #18615
lemma ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [Zero s] (h0 : (0 : s) = (0 : 𝕜))
    [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id h0) = ⊤ :=
  SetLike.ext'_iff.mpr (adjoin_id_dense h0).closure_eq

open scoped NonUnitalContinuousFunctionalCalculus in
theorem cfcₙHom_range {a : A} (ha : p a) :
    NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) = elemental 𝕜 a := by
  rw [NonUnitalStarAlgHom.range_eq_map_top, ← ContinuousMapZero.elemental_eq_top rfl, NonUnitalStarAlgebra.elemental,
    ← NonUnitalStarSubalgebra.topologicalClosure_map _ _ (cfcₙHom_isClosedEmbedding ha (R := 𝕜)),
    NonUnitalStarAlgHom.map_adjoin]
  congr
  simpa using cfcₙHom_id ha

variable {𝕜}

open scoped ContinuousMapZero

theorem cfcₙHom_apply_mem_elemental {a : A} (ha : p a) (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙHom ha f ∈ elemental 𝕜 a :=
  cfcₙHom_range 𝕜 ha ▸ ⟨f, rfl⟩

variable [T2Space A]

open NonUnitalStarSubalgebra elemental in
theorem commute_cfcₙHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(σₙ 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  have hb : b ∈ centralizer 𝕜 {a} := by simpa [mem_centralizer_iff] using ⟨hb₁.eq, hb₂.eq⟩
  le_centralizer_centralizer 𝕜 a (cfcₙHom_apply_mem_elemental ha f) b (.inl hb) |>.symm

protected theorem IsSelfAdjoint.commute_cfcₙHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(σₙ 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  commute_cfcₙHom ha hb (ha'.star_eq.symm ▸ hb) f

theorem commute_cfcₙ {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf₀ ha ↦ commute_cfcₙHom ha hb₁ hb₂ ⟨⟨_, hf.restrict⟩, hf₀⟩

protected theorem IsSelfAdjoint.commute_cfcₙ {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  commute_cfcₙ hb₁ (ha.star_eq.symm ▸ hb₁) f
