import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # range of the continuous functional calculus

This file contains results about the range of the continuous functional calculus, and consequences thereof.
-/

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
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure, ←
    StarSubalgebra.topologicalClosure_map _ _ (cfcHom_isClosedEmbedding ha (R := 𝕜)),
    polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  congr
  rw [Set.image_singleton, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_X_eq_restrict_id, cfcHom_id ha]

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
