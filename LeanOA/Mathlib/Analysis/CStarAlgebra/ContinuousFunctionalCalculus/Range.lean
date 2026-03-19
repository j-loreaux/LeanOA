/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/- The primed versions of these lemmas should replace the originals in Mathlib. -/


public section

open Topology

open scoped CStarAlgebra

section Bar

section Unital

section RCLike

variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [StarModule 𝕜 A]
variable [ContinuousFunctionalCalculus 𝕜 A p]
variable [IsTopologicalRing A] [ContinuousStar A]

open StarAlgebra

open scoped ContinuousFunctionalCalculus in
theorem range_cfcHom_le {a : A} (ha : p a) :
    (cfcHom ha (R := 𝕜)).range ≤ elemental 𝕜 a := by
  grw [StarAlgHom.range_eq_map_top, ← ContinuousMap.elemental_id_eq_top, StarAlgebra.elemental,
    StarSubalgebra.map_topologicalClosure_le _ _ (cfcHom_continuous ha (R := 𝕜)),
    StarAlgHom.map_adjoin]
  simp [cfcHom_id ha, elemental]

lemma range_cfc_subset {a : A} (ha : p a) : Set.range (cfc (R := 𝕜) · a) ⊆ elemental 𝕜 a := by
  grw [range_cfc_eq_range_cfcHom 𝕜 ha, range_cfcHom_le 𝕜 ha]

variable {𝕜}

theorem cfcHom_apply_mem_elemental' {a : A} (ha : p a) (f : C(spectrum 𝕜 a, 𝕜)) :
    cfcHom ha f ∈ elemental 𝕜 a :=
  range_cfcHom_le 𝕜 ha ⟨f, rfl⟩

@[simp, grind ←]
theorem cfc_apply_mem_elemental' (f : 𝕜 → 𝕜) (a : A) :
    cfc f a ∈ elemental 𝕜 a :=
  cfc_cases _ a f (zero_mem _) fun hf ha ↦
    cfcHom_apply_mem_elemental' ha ⟨_, hf.restrict⟩

lemma cfc_mem {S : Type*} [SetLike S A] [SubringClass S A] [SMulMemClass S 𝕜 A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] (f : 𝕜 → 𝕜) (a : A) (has : a ∈ s) :
    cfc f a ∈ s :=
  StarSubalgebra.topologicalClosure_minimal (t := .ofClass s) (by simpa) (by simpa)
    (cfc_apply_mem_elemental' f a)

-- this should probably be an instance?
attribute [instance] StarAlgebra.elemental.isClosed

end RCLike

open scoped NNReal
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
variable [ClosedEmbeddingContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A]
variable [T2Space A] [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

lemma range_cfc_nnreal_eq_image_cfc_real' (a : A) (ha : 0 ≤ a) :
    Set.range (cfc (R := ℝ≥0) · a) = (cfc · a) '' {f | ∀ x ∈ spectrum ℝ a, 0 ≤ f x} := by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    simp only [cfc_nnreal_eq_real f a ha]
    exact ⟨_, fun _ _ ↦ by positivity, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    simp only [cfc_real_eq_nnreal a hf]
    exact ⟨_, rfl⟩

variable [ContinuousStar A] [StarModule ℝ A]

lemma range_cfc_nnreal' (a : A) (ha : 0 ≤ a) :
    Set.range (cfc (R := ℝ≥0) · a) ⊆ {x | x ∈ StarAlgebra.elemental ℝ a ∧ 0 ≤ x} := by
  grw [range_cfc_nnreal_eq_image_cfc_real' a ha, Set.setOf_and, SetLike.setOf_mem_eq,
    ← range_cfc_subset ℝ ha.isSelfAdjoint, Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact Set.image_mono fun _ ↦ cfc_nonneg

end Unital

end Bar

section NonUnital

section RCLike

variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A]
variable [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
variable [ContinuousConstSMul 𝕜 A] [StarModule 𝕜 A] [IsTopologicalRing A] [ContinuousStar A]

open NonUnitalStarAlgebra

open scoped NonUnitalContinuousFunctionalCalculus in
theorem range_cfcₙHom_le {a : A} (ha : p a) :
    NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) ≤ elemental 𝕜 a := by
  grw [← NonUnitalStarAlgebra.map_top, ← ContinuousMapZero.elemental_eq_top,
    NonUnitalStarAlgebra.elemental,
    NonUnitalStarSubalgebra.map_topologicalClosure_le (R := 𝕜) _ (cfcₙHom_continuous ha),
    NonUnitalStarAlgHom.map_adjoin]
  simp [cfcₙHom_id ha, elemental]

theorem range_cfcₙ_subset {a : A} (ha : p a) : Set.range (cfcₙ (R := 𝕜) · a) ⊆ elemental 𝕜 a := by
  grw [range_cfcₙ_eq_range_cfcₙHom 𝕜 ha, range_cfcₙHom_le 𝕜 ha]

variable {𝕜}

open scoped ContinuousMapZero

theorem cfcₙHom_apply_mem_elemental' {a : A} (ha : p a) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    cfcₙHom ha f ∈ elemental 𝕜 a :=
  range_cfcₙHom_le 𝕜 ha ⟨f, rfl⟩

@[simp, grind ←]
theorem cfcₙ_apply_mem_elemental' (f : 𝕜 → 𝕜) (a : A) :
    cfcₙ f a ∈ elemental 𝕜 a :=
  cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha ↦
    cfcₙHom_apply_mem_elemental' ha ⟨⟨_, hf.restrict⟩, hf₀⟩

lemma cfcₙ_mem {S : Type*} [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S 𝕜 A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] (f : 𝕜 → 𝕜) (a : A) (has : a ∈ s) :
    cfcₙ f a ∈ s :=
  NonUnitalStarSubalgebra.topologicalClosure_minimal (t := .ofClass s) _ (by simpa) (by simpa)
    (cfcₙ_apply_mem_elemental' f a)

end RCLike

open scoped NNReal
variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
variable [SMulCommClass ℝ A A] [TopologicalSpace A]
variable [NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [IsTopologicalRing A] [T2Space A] [PartialOrder A] [NonnegSpectrumClass ℝ A]
variable [StarOrderedRing A]

lemma range_cfcₙ_nnreal_eq_image_cfcₙ_real' (a : A) (ha : 0 ≤ a) :
    Set.range (cfcₙ (R := ℝ≥0) · a) = (cfcₙ · a) '' {f | ∀ x ∈ quasispectrum ℝ a, 0 ≤ f x} := by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    simp only [cfcₙ_nnreal_eq_real f a]
    exact ⟨_, fun _ _ ↦ by positivity, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    simp only [cfcₙ_real_eq_nnreal a hf]
    exact ⟨_, rfl⟩

variable [StarModule ℝ A] [ContinuousStar A] [ContinuousConstSMul ℝ A]

lemma range_cfcₙ_nnreal' (a : A) (ha : 0 ≤ a) :
    Set.range (cfcₙ (R := ℝ≥0) · a) ⊆ {x | x ∈ NonUnitalStarAlgebra.elemental ℝ a ∧ 0 ≤ x} := by
  grw [range_cfcₙ_nnreal_eq_image_cfcₙ_real' a ha, Set.setOf_and, SetLike.setOf_mem_eq,
    ← range_cfcₙ_subset _ ha.isSelfAdjoint, Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact Set.image_mono fun _ ↦ cfcₙ_nonneg

end NonUnital
