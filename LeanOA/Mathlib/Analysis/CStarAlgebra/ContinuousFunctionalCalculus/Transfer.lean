import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import LeanOA.Mathlib.Algebra.Star.StarAlgHom
import LeanOA.Mathlib.Topology.ContinuousMap.ContinuousMapZero

section UnitalTransfer

variable {R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  [instCFC : ContinuousFunctionalCalculus R A p]

@[simps!]
noncomputable def cfcHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : C(spectrum R b, R) →⋆ₐ[R] B :=
  (Homeomorph.setCongr (by simp)).compStarAlgEquiv' R R |>.arrowCongr
    e (cfcHom (hpq (e.symm b) |>.mpr <| by simpa))

lemma continuous_cfcHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) (he : Continuous e) : Continuous (cfcHomTransfer e hpq b hb) :=
  (he.comp <| cfcHom_continuous _).comp <| ContinuousMap.continuous_precomp _

omit [TopologicalSpace B] in
lemma cfcHomTransfer_injective (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : Function.Injective (cfcHomTransfer e hpq b hb) :=
  e.injective.comp (cfcHom_injective _) |>.comp <| Equiv.injective _

omit [TopologicalSpace B] in
lemma cfcHomTransfer_id (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcHomTransfer e hpq b hb (.restrict (spectrum R b) (.id R) ) = b := by
  convert e.apply_symm_apply b
  congrm(e $(cfcHom_id _))

open ContinuousFunctionalCalculus in
/-- Transfer a continuous functional calculus instance to a type synonym with
a weaker topology. -/
theorem ContinuousFunctionalCalculus.transfer (e : A ≃⋆ₐ[R] B)
    (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) :
    ContinuousFunctionalCalculus R B q where
  predicate_zero := map_zero e ▸ (hpq 0 |>.mp instCFC.predicate_zero)
  compactSpace_spectrum b := by
    rw [← isCompact_iff_compactSpace, ← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    exact isCompact_spectrum (e.symm b)
  spectrum_nonempty b hb := by
    rw [← e.apply_symm_apply b, AlgEquiv.spectrum_eq]
    have := e.nontrivial
    exact spectrum_nonempty (e.symm b) <| by simpa [hpq]
  exists_cfc_of_predicate b hb :=
    have ha : p (e.symm b) := by simpa [hpq]
    ⟨cfcHomTransfer e hpq b hb,
      continuous_cfcHomTransfer e hpq b hb he,
      cfcHomTransfer_injective e hpq b hb,
      cfcHomTransfer_id e hpq b hb,
      fun f ↦ by simp [cfcHom_map_spectrum ha],
      fun f ↦ by simp [← hpq, cfcHom_predicate ha]⟩

lemma cfcHom_eq_cfcHomTransfer [ContinuousFunctionalCalculus R B q] [ContinuousMap.UniqueHom R B]
    (e : A ≃⋆ₐ[R] B) (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcHom hb = cfcHomTransfer e hpq b hb := by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact continuous_cfcHomTransfer e hpq b hb he
  · exact cfcHomTransfer_id e hpq b hb

lemma cfc_eq_cfc_transfer [ContinuousFunctionalCalculus R B q] [ContinuousMap.UniqueHom R B]
    (e : A ≃⋆ₐ[R] B) (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) (f : R → R) (b : B) :
    cfc f b = e (cfc f (e.symm b)) := by
  obtain (⟨hb, hf⟩ | hb | hf) :
      (q b ∧ ContinuousOn f (spectrum R b)) ∨ ¬ q b ∨ ¬ ContinuousOn f (spectrum R b) := by
    tauto
  · have ha : p (e.symm b) := by simpa [hpq]
    have hf' : ContinuousOn f (spectrum R (e.symm b)) := by rwa [AlgEquiv.spectrum_eq]
    rw [cfc_apply f b, cfcHom_eq_cfcHomTransfer e he hpq b hb, cfc_apply f (e.symm b)]
    congr!
  · rw [cfc_apply_of_not_predicate b hb, cfc_apply_of_not_predicate (e.symm b) (by simpa [hpq]),
      map_zero e]
  · rw [cfc_apply_of_not_continuousOn b hf,
      cfc_apply_of_not_continuousOn (e.symm b) (by simpa [AlgEquiv.spectrum_eq] using hf),
      map_zero e]


end UnitalTransfer

section NonUnitalTransfer

open scoped ContinuousMapZero

variable {R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R]
  [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [StarRing B] [TopologicalSpace B]
  [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [instCFC : NonUnitalContinuousFunctionalCalculus R A p]

-- `AlgEquiv` is too strong. That's terrible. We shouldn't need `Star` here
@[simp]
lemma AlgEquiv.quasispectrum_eq {F R A B : Type*} [CommSemiring R] [NonUnitalRing A]
    [NonUnitalRing B] [Module R A] [Module R B] [Star A] [Star B] [EquivLike F A B]
    [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B]
    (f : F) (a : A) : quasispectrum R (f a) = quasispectrum R a := by
  let e := StarAlgEquivClass.toStarAlgEquiv f
  apply subset_antisymm
  · exact NonUnitalAlgHom.quasispectrum_apply_subset' R e a
  · simpa using NonUnitalAlgHom.quasispectrum_apply_subset' R e.symm (e a)

@[simps!]
noncomputable def cfcₙHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : C(quasispectrum R b, R)₀ →⋆ₙₐ[R] B :=
  ContinuousMapZero.starAlgEquiv_precomp R
    (Homeomorph.setCongr (by simp)) (by ext; simp [Homeomorph.setCongr]) |>.arrowCongr'
    e (cfcₙHom (hpq (e.symm b) |>.mpr <| by simpa))

omit [IsScalarTower R B B] [SMulCommClass R B B] in
lemma continuous_cfcₙHomTransfer (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) (he : Continuous e) : Continuous (cfcₙHomTransfer e hpq b hb) :=
  (he.comp <| cfcₙHom_continuous _).comp <| ContinuousMapZero.continuous_precomp _

omit [TopologicalSpace B] [IsScalarTower R B B] [SMulCommClass R B B] in
lemma cfcₙHomTransfer_injective (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x))
    (b : B) (hb : q b) : Function.Injective (cfcₙHomTransfer e hpq b hb) :=
  e.injective.comp (cfcₙHom_injective _) |>.comp <| Equiv.injective _

omit [TopologicalSpace B] [IsScalarTower R B B] [SMulCommClass R B B] in
lemma cfcₙHomTransfer_id (e : A ≃⋆ₐ[R] B) (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcₙHomTransfer e hpq b hb (.id (quasispectrum R b)) = b := by
  convert e.apply_symm_apply b
  congrm(e $(cfcₙHom_id _))

open NonUnitalContinuousFunctionalCalculus in
/-- Transfer a continuous functional calculus instance to a type synonym with
a weaker topology. -/
theorem NonUnitalContinuousFunctionalCalculus.transfer (e : A ≃⋆ₐ[R] B)
    (he : Continuous e) (hpq : ∀ x, p x ↔ q (e x)) :
    NonUnitalContinuousFunctionalCalculus R B q where
  predicate_zero := map_zero e ▸ (hpq 0 |>.mp instCFC.predicate_zero)
  compactSpace_quasispectrum b := by
    rw [← isCompact_iff_compactSpace, ← e.apply_symm_apply b, AlgEquiv.quasispectrum_eq]
    exact isCompact_quasispectrum (e.symm b)
  exists_cfc_of_predicate b hb :=
    have ha : p (e.symm b) := by simpa [hpq]
    ⟨cfcₙHomTransfer e hpq b hb,
      continuous_cfcₙHomTransfer e hpq b hb he,
      cfcₙHomTransfer_injective e hpq b hb,
      cfcₙHomTransfer_id e hpq b hb,
      fun f ↦ by simp [cfcₙHom_map_quasispectrum ha, ContinuousMapZero.starAlgEquiv_precomp],
      fun f ↦ by simp [← hpq, cfcₙHom_predicate ha]⟩

lemma cfcₙHom_eq_cfcₙHomTransfer [NonUnitalContinuousFunctionalCalculus R B q]
    [ContinuousMapZero.UniqueHom R B] (e : A ≃⋆ₐ[R] B) (he : Continuous e)
    (hpq : ∀ x, p x ↔ q (e x)) (b : B) (hb : q b) :
    cfcₙHom hb = cfcₙHomTransfer e hpq b hb := by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact continuous_cfcₙHomTransfer e hpq b hb he
  · exact cfcₙHomTransfer_id e hpq b hb

lemma cfcₙ_eq_cfcₙ_transfer [NonUnitalContinuousFunctionalCalculus R B q]
    [ContinuousMapZero.UniqueHom R B] (e : A ≃⋆ₐ[R] B) (he : Continuous e)
    (hpq : ∀ x, p x ↔ q (e x)) (f : R → R) (b : B) :
    cfcₙ f b = e (cfcₙ f (e.symm b)) := by
  obtain (⟨hb, hf, hf0⟩ | hb | hf | hf0) :
      (q b ∧ ContinuousOn f (quasispectrum R b) ∧ f 0 = 0) ∨
        ¬ q b ∨ ¬ ContinuousOn f (quasispectrum R b) ∨ ¬ f 0 = 0 := by
    tauto
  · have ha : p (e.symm b) := by simpa [hpq]
    have hf' : ContinuousOn f (quasispectrum R (e.symm b)) := by rwa [AlgEquiv.quasispectrum_eq]
    rw [cfcₙ_apply f b, cfcₙHom_eq_cfcₙHomTransfer e he hpq b hb, cfcₙ_apply f (e.symm b)]
    congr!
  · rw [cfcₙ_apply_of_not_predicate b hb, cfcₙ_apply_of_not_predicate (e.symm b) (by simpa [hpq]),
      map_zero e]
  · rw [cfcₙ_apply_of_not_continuousOn b hf,
      cfcₙ_apply_of_not_continuousOn (e.symm b) (by simpa [AlgEquiv.quasispectrum_eq] using hf),
      map_zero e]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0, cfcₙ_apply_of_not_map_zero _ hf0, map_zero e]

end NonUnitalTransfer
