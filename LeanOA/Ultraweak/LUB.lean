import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace


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

open Filter in
omit [StarOrderedRing M] [CompleteSpace P] in
/-- A filter is cauchy relative to the `WeakE M P` topology if and only if
mapping it through `φ` is cauchy for every `φ : σ(M, P) →P[ℂ] ℂ`. -/
private lemma cauchy_weakE_iff_forall_posCLM {l : Filter (WeakE M P)} :
    Cauchy l ↔ ∀ φ : σ(M, P) →P[ℂ] ℂ,
      Cauchy (Filter.map (fun m ↦ φ (toUltraweak ℂ P m)) l) := by
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

-- we're missing `WeakBilin` API
private noncomputable def weakEEquiv : WeakE M P ≃ₗ[ℂ] M := .refl ℂ _

-- ugh, `WeakBilin` has some nasty defeq abuse.
-- we should get this out of tactic mode as a proof.
private noncomputable def weakEUniformEquiv :
    (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) ≃ᵤ
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) 1)) := by
  let e : (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) ≃
      (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) 1)) :=
    { toFun := Subtype.map ((weakEEquiv M P).symm ∘ ofUltraweak) fun _ ↦ id
      invFun := Subtype.map (toUltraweak ℂ P ∘ weakEEquiv M P) (by simp)
      left_inv _ := by ext; simp
      right_inv _ := by ext; simp }
  have := isCompact_iff_compactSpace.mp <| isCompact_closedBall ℂ P (0 : M) 1
  refine Continuous.uniformOfEquivCompactToT2 e ?_
  rw [continuous_induced_rng, Function.comp_def]
  refine WeakBilin.continuous_of_continuous_eval _ fun ⟨φ, hφ⟩ ↦ ?_
  exact (map_continuous φ).comp continuous_subtype_val

end Ultraweak
