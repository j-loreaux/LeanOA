import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import LeanOA.ContinuousMap.Uniform

open Filter Topology

section Unital

section Generic

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

open scoped ContinuousFunctionalCalculus

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`. -/
theorem tendsto_cfc {l : Filter X} (F : X → R → R) (f : R → R) (a : A)
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : ∀ x, ContinuousOn (F x) (spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
  by_cases ha : p a
  · conv =>
      enter [1, x]
      rw [cfc_apply (hf := hF x)]
    rw [cfc_apply ..]
    apply cfcHom_continuous _ |>.tendsto _ |>.comp
    rwa [hf.tendsto_restrict_iff_tendstoUniformlyOn hF]
  · simpa [cfc_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀`. -/
theorem continuousAt_cfc [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ :=
  tendsto_cfc f (f x₀) a h_tendsto hf (hf x₀)

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum, then `-/
theorem continuous_cfc [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  rw [continuous_iff_continuousAt] at h_cont ⊢
  simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Set.mem_singleton_iff, toFun_ofFun, forall_eq] at h_cont
  exact fun x ↦ continuousAt_cfc f a x (h_cont x)

end Generic

section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

open scoped ContinuousFunctionalCalculus

theorem continuous_cfcHomSuperset [TopologicalSpace X] (s : Set 𝕜) (hs : IsCompact s) (f : C(s, 𝕜))
    (a : C(X, A)) (ha' : ∀ x, p (a x)) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s) :
    Continuous (fun x ↦ cfcHomSuperset (ha' x) (ha x) f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.commutes] using continuous_const
  | id =>
    simp only [cfcHomSuperset_id]
    fun_prop
  | star_id =>
    simp only [map_star, cfcHomSuperset_id]
    fun_prop
  | add f g hf hg => simpa using hf.add hg
  | mul f g hf hg => simpa using hf.mul hg
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcHom (ha' x)))]
    rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

end RCLike

end Unital

section NonUnital

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

-- we should also have a generic `tendsto` lemma.

open scoped NonUnitalContinuousFunctionalCalculus in
theorem continuousAt_cfcₙ [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    ContinuousAt (fun x ↦ cfcₙ (f x) a) x₀ := by
  sorry

open scoped NonUnitalContinuousFunctionalCalculus in
open UniformOnFun in
theorem continuous_cfcₙ [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {quasispectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    Continuous fun x ↦ cfcₙ (f x) a := by
  sorry

end NonUnital
