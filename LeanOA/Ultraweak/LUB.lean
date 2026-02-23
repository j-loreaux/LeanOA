import LeanOA.Ultraweak.SeparatingDual
import LeanOA.WeakDual.UniformSpace
import LeanOA.ComplexOrder
import LeanOA.StarOrderedRing
import LeanOA.CFC

variable {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
  [StarRing R] [StarRing A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

class NonUnitalStarSubalgebra.IsMasa (B : NonUnitalStarSubalgebra R A) : Prop where
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  maximal (C : NonUnitalStarSubalgebra R A) (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
      (hBC : B ≤ C) : C ≤ B

theorem exists_le_masa (B : {C : NonUnitalStarSubalgebra R A // (∀ x ∈ C, ∀ y ∈ C, x * y = y * x)}) :
    ∃ (C : NonUnitalStarSubalgebra R A), B ≤ C ∧ C.IsMasa  := by
  obtain ⟨C, hC⟩ := by
    refine zorn_le (α := {C : NonUnitalStarSubalgebra R A // (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ B ≤ C}) ?_
    intro chain hchain
    obtain (rfl | h) := chain.eq_empty_or_nonempty
    · exact ⟨⟨B.val, B.prop, le_rfl⟩, by simp⟩
    · have := h.to_subtype
      have hdir : Directed (· ≤ ·) fun S : chain ↦ S.val.val :=
        hchain.directedOn.directed_val.mono_comp _ (by simp)
      let bound : NonUnitalStarSubalgebra R A := ⨆ S : chain, S
      refine ⟨⟨bound, ?_, ?_⟩, ?_⟩
      · simp only [bound]
        intro a ha b hb
        rw [← SetLike.mem_coe, NonUnitalStarSubalgebra.coe_iSup_of_directed hdir,
          Set.mem_iUnion] at ha hb
        obtain ⟨S, hS⟩ := ha
        obtain ⟨T, hT⟩ := hb
        obtain ⟨V, hV, hSV, hTV⟩ := hchain.directedOn _ S.prop _ T.prop
        exact V.prop.1 _ (hSV hS) _ (hTV hT)
      · exact Classical.arbitrary chain |>.val.prop.2 |>.trans <|
          le_iSup (fun S : chain ↦ S.val.val) _
      · intro S hS
        lift S to chain using hS
        exact le_iSup (fun S : chain ↦ S.val.val) _
  exact ⟨C, C.prop.2, ⟨C.prop.1, fun S h_comm hCS ↦ @hC ⟨S, h_comm, C.prop.2.trans hCS⟩ hCS⟩⟩


#exit
namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
that `g` is the inverse of `f`. -/
@[simps apply]
def ofHomInv' (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ ≤ g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
theorem ofHomInv'_symm_apply (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
    (a : β) : (ofHomInv f g h₁ h₂).symm a = g a := rfl

end OrderIso

namespace OrderHom

variable {α : Type*} [Preorder α]

instance : Mul (α →o α) where mul f g := f.comp g
instance : One (α →o α) where one := .id

@[simp] lemma mul_apply (f g : α →o α) (x : α) : (f * g) x = f (g x) := rfl
@[simp] lemma one_apply (x : α) : (1 : α →o α) x = x := rfl

lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
lemma one_eq_id : (1 : α →o α) = .id := rfl

instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom

namespace OrderIso

variable {α : Type*} [Preorder α]

instance : Mul (α ≃o α) where mul f g := g.trans f
instance : One (α ≃o α) where one := refl α
instance : Inv (α ≃o α) where inv := symm

@[simp] lemma mul_apply (f g : α ≃o α) (x : α) : (f * g) x = f (g x) := rfl
@[simp] lemma one_apply (x : α) : (1 : α ≃o α) x = x := rfl
@[simp] lemma inv_apply' (f : α ≃o α) (x : α) : f⁻¹ x = f.symm x := rfl

lemma mul_eq_trans (f g : α ≃o α) : (f * g : α ≃o α) = g.trans f := rfl
lemma one_eq_refl : (1 : α ≃o α) = refl α := rfl
lemma inv_eq_symm (f : α ≃o α) : f⁻¹ = f.symm := rfl

instance : Group (α ≃o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]
  inv_mul_cancel f := by simp [DFunLike.ext_iff]

end OrderIso

namespace StarOrderedRing

section NonUnital

variable {R : Type*} [NonUnitalRing R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The map `x ↦ r * x * star r` as an order homomorphism in a star-ordered ring. -/
@[simps]
def conjOrderHom (r : R) : R →o R where
  toFun x := r * x * star r
  monotone' _ _ h := star_right_conjugate_le_conjugate h r

lemma conjOrderHom_mul (r s : R) :
    conjOrderHom (r * s) = (conjOrderHom r).comp (conjOrderHom s) := by
  ext; simp [mul_assoc]

/-- The map `r x ↦ r * x * star r` as a semigroup homomorphism from `R` into `R →o R`. -/
@[simps]
def conjOrderHomMulHom : R →ₙ* R →o R where
  toFun := conjOrderHom
  map_mul' := conjOrderHom_mul

end NonUnital

section Unital

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

@[simp]
lemma conjOrderHom_one : conjOrderHom (1 : R) = .id := by ext; simp

/-- The map `r x ↦ r * x * star r` as a monoid homomorphism from `R` into `R →o R`. -/
@[simps]
def conjOrderHomMonoidHom : R →* R →o R where
  toFun := conjOrderHom
  map_mul' := conjOrderHom_mul
  map_one' := conjOrderHom_one

@[simp]
lemma toMulHom_conjOrderHomMonoidHom :
    (conjOrderHomMonoidHom (R := R)).toMulHom = conjOrderHomMulHom :=
  rfl

/-- The map  `r x ↦ r * x * star r` as a group homomorphism from `Rˣ` into `R ≃o R`
in a star-ordered ring `R`. -/
def conjUnitsOrderIso : Rˣ →* (R ≃o R) where
  toFun r := .ofHomInv' (conjOrderHomMonoidHom (r : R)) (conjOrderHomMonoidHom (↑r⁻¹ : R))
    (by rw [← OrderHom.mul_eq_comp, ← map_mul]; simp)
    (by rw [← OrderHom.mul_eq_comp, ← map_mul]; simp)
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

lemma _root_.IsLUB.conjugate_star_right_of_isUnit {s : Set R} {x : R}
      (h : IsLUB s x) (r : R) (hr : IsUnit r) :
    IsLUB (conjOrderHom r '' s) (r * x * star r) := by
  lift r to Rˣ using hr
  exact (conjUnitsOrderIso r).isLUB_image'.mpr h

end Unital

--- we could also turn `conjOrderHom` into a `PositiveLinearMap`, which we should do.
end StarOrderedRing

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

open Filter Topology in
private lemma tendsto_weakE_iff_forall_posCLM {α : Type*} [TopologicalSpace α]
    {l : Filter α} (x : WeakE M P) {f : α → WeakE M P} :
    Tendsto f l (𝓝 x) ↔ ∀ φ : σ(M, P) →P[ℂ] ℂ,
      Tendsto (fun m ↦ φ (toUltraweak ℂ P (weakEEquiv M P (f m)))) l
        (𝓝 (φ (toUltraweak ℂ P (weakEEquiv M P x)))) := by
  rw [WeakBilin.tendsto_iff_forall_eval_tendsto (fromEₗ M P) (fromEₗ_injective M P)]
  refine ⟨fun h φ ↦ h ⟨φ.toContinuousLinearMap, Submodule.subset_span <| by simp⟩,
    fun h ⟨φ, hφ⟩ ↦ ?_⟩
  simp only [fromEₗ_apply_apply]
  induction hφ using Submodule.span_induction with
  | mem φ hφ => obtain ⟨φ, hφ, rfl⟩ := hφ; exact h φ
  | zero => exact h 0
  | add φ ψ hφ hψ ihφ ihψ => simpa using ihφ.add ihψ
  | smul a φ hφ ihφ => simpa using ihφ.const_smul a

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

private lemma isCompact_weakE_closedBall (r : ℝ) :
    IsCompact (weakEEquiv M P ⁻¹' Metric.closedBall (0 : M) r) := by
  have := Ultraweak.isCompact_closedBall ℂ P (0 : M) r
  rw [isCompact_iff_compactSpace] at this ⊢
  exact weakEUniformEquiv M P r |>.toHomeomorph.compactSpace

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

open Filter in
/-- A bounded filter `l` in `σ(M, P)` is cauchy if and only if `map φ l` is cauchy in `ℂ`
for every positive continuous linear functional `φ`. -/
lemma cauchy_of_forall_posCLM_cauchy_map {l : Filter σ(M, P)} {r : ℝ}
    (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r))
    (hl : ∀ φ : σ(M, P) →P[ℂ] ℂ, Cauchy (map φ l)) :
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

open Filter in
/-- A bounded filter `l` in `σ(M, P)` is cauchy if and only if `map φ l` is cauchy in `ℂ`
for every positive continuous linear functional `φ`. -/
lemma cauchy_of_forall_posCLM_cauchy_map' {l : Filter σ(M, P)} {s : Set M}
    (hs : Bornology.IsBounded s) (hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' s))
    (hl : ∀ φ : σ(M, P) →P[ℂ] ℂ, Cauchy (map φ l)) :
    Cauchy l := by
  obtain ⟨r, hr⟩ := hs |>.subset_closedBall 0
  replace hlr : l ≤ 𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r) := hlr.trans <| by simpa
  have key : Cauchy (map ((weakEEquiv M P).symm ∘ ofUltraweak) l) := by
    rw [cauchy_weakE_iff_forall_posCLM]
    simpa [Function.comp_def]
  have hlr' : map ((weakEEquiv M P).symm ∘ ofUltraweak) l ≤
      𝓟 (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)) :=
    map_mono hlr |>.trans <|
      mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall M P r |>.tendsto
  simpa using key.map_of_le
    (uniformContinuousOn_toUltraweak_comp_weakEEquiv M P r) hlr'

attribute [push] Filter.not_neBot
attribute [push ←] Filter.neBot_iff

#check tendsto_nhdsWithin_iff

-- this proof is totally gross
open Filter Topology in
private lemma tendsto_of_forall_posCLM {α : Type*} [TopologicalSpace α]
    {l : Filter α} (x : σ(M, P)) {f : α → σ(M, P)} {r : ℝ}
    (hfl : Tendsto f l (𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) r)))
    (hf : ∀ φ : σ(M, P) →P[ℂ] ℂ, Tendsto (fun m ↦ φ (f m)) l (𝓝 (φ x))) :
    Tendsto f l (𝓝 x) := by
  by_cases! h_bot : l = ⊥
  · simp [h_bot]
  have key : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓝 ((weakEEquiv M P).symm (ofUltraweak x))) := by
    rw [tendsto_weakE_iff_forall_posCLM]
    simpa [Function.comp_def]
  have hfl' : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓟 (weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r))) :=
    map_mono hfl |>.trans <|
      mapsTo_weakEEquiv_symm_comp_ofUltraweak_preimage_closedBall M P r |>.tendsto
  have := (uniformContinuousOn_toUltraweak_comp_weakEEquiv M P r).continuousOn
  have hx : (weakEEquiv M P).symm (ofUltraweak x) ∈
      weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r) :=
    isCompact_weakE_closedBall M P r |>.isClosed.mem_of_tendsto key <| by
      simpa using hfl'
  have := this _ hx |>.tendsto
  have key2 : Tendsto (fun m : α ↦ (weakEEquiv M P).symm (ofUltraweak (f m))) l
      (𝓝[weakEEquiv M P ⁻¹' (Metric.closedBall (0 : M) r)]
        ((weakEEquiv M P).symm (ofUltraweak x))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨key, by simpa using hfl'⟩
  simpa using this.comp key2

open scoped ComplexStarModule

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

open Filter Topology Set in
/-- An increasing net of elements which is bounded above in `σ(M, P)` converges
to its least upper bound.

I'll note that this uses that `σ(M, P)` is an `OrderClosedTopology` to conclude
the element to which is converges is indeed the least upper bound. -/
lemma DirectedOn.exists_isLUB (s : Set σ(M, P)) (hs : DirectedOn (· ≤ ·) s)
    (hnon : s.Nonempty) (hbd : BddAbove s) :
    ∃ x : σ(M, P), IsLUB s x ∧ Tendsto (Subtype.val : s → σ(M, P)) atTop (𝓝 x) := by
  /- Since `s` is nonempty, we may take the intersection with `Ici x₀` for some
  `x₀ ∈ s`. This set is still directed, but now it is also bounded above and below.
  Hence it is norm bounded. -/
  let ⟨x₀, hx₀⟩ := hnon
  have hbd' : BddAbove (ofUltraweak '' (s ∩ Ici x₀)) :=
    monotone_ofUltraweak.map_bddAbove hbd.inter_of_left
  have hbd'' : BddBelow (ofUltraweak '' (s ∩ Ici x₀)) := by
    use ofUltraweak x₀
    rintro - ⟨x, hx, rfl⟩
    aesop
  obtain ⟨r, hr⟩ := isBounded_of_bddAbove_of_bddBelow hbd' hbd'' |>.subset_closedBall 0
  /- The net `s` of elements is eventually bounded. -/
  have h_map_le : map (Subtype.val : s → σ(M, P)) atTop ≤
      𝓟 (ofUltraweak ⁻¹' Metric.closedBall 0 r) := by
    simp only [le_principal_iff, mem_map]
    refine mem_of_superset (Ici_mem_atTop (⟨x₀, hx₀⟩ : s)) ?_
    intro ⟨x, hx⟩ hxx₀
    simp only [mem_Ici, Subtype.mk_le_mk, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] at hxx₀ ⊢
    simpa using hr ⟨_, ⟨hx, hxx₀⟩, rfl⟩
  /- The subtype `↥s` is directed and nonempty. -/
  have : IsDirectedOrder s := ⟨hs.directed_val⟩
  have : Nonempty s := hnon.to_subtype
  /- To see that the net `s` is cauchy in `σ(M, P)` it suffices to check that for
  any continuous positive linear functional `φ`, applying `φ` to `s` is also cauchy.
  However, since this is a net in `ℂ` which is bounded above, it in fact converges,
  and is therefore cauchy. -/
  have h_cauchy : Cauchy (map ((↑) : s → σ(M, P)) atTop) := by
    apply cauchy_of_forall_posCLM_cauchy_map M P h_map_le fun φ ↦ ?_
    have hφ := OrderHomClass.mono φ
    exact Tendsto.cauchy_map <| tendsto_atTop_ciSup' (hφ.comp (Subtype.mono_coe s)) <| by
      simpa [← Function.comp_def, Set.range_comp]
        using (OrderHomClass.mono φ |>.map_bddAbove hbd)
  /- Since the closed ball is compact (and therefore complete) and this cauchy net is
  eventually within it, it converges to some element `x`. -/
  obtain ⟨x, -, hx⟩ := isCompact_closedBall ℂ P (0 : M) r |>.isComplete _ h_cauchy h_map_le
  refine ⟨x, ?_, hx⟩
  /- Since the net is increasing, and the topology on `σ(M, P)` is order closed, the
  limit is the least upper bound. -/
  simpa [setOf] using isLUB_of_tendsto_atTop' (β := s) (Subtype.mono_coe s) hx

/-- `σ(M, P)` is a conditionally complete partial order. Since this is only dependent upon the
order, not the topology, the same is true of `M`. -/
noncomputable instance : ConditionallyCompletePartialOrderSup σ(M, P) where
  sSup s :=
    open Classical in
    if h : DirectedOn (· ≤ ·) s ∧ s.Nonempty ∧ BddAbove s
    then (DirectedOn.exists_isLUB M P s h.1 h.2.1 h.2.2).choose
    else 0
  isLUB_csSup_of_directed s h_dir h_non hbdd := by
    rw [dif_pos (by grind)]
    exact (DirectedOn.exists_isLUB M P s h_dir h_non hbdd).choose_spec.1


open Filter in
/-- An increasing net of elements which is bounded above in `σ(M, P)` converges
to its least upper bound. -/
instance : SupConvergenceClass σ(M, P) where
  tendsto_coe_atTop_isLUB a s hsa := by
    by_cases! h : (atTop : Filter s) = ⊥
    · simp [h]
    rw [atTop_neBot_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    replace h₁ : s.Nonempty := Set.nonempty_coe_sort.mp h₁
    replace h₂ : DirectedOn (· ≤ ·) s := by
      rw [directedOn_iff_directed]
      obtain ⟨h₂⟩ := h₂
      exact h₂
    obtain ⟨u, hu₁, hu₂⟩ := DirectedOn.exists_isLUB M P s h₂ h₁ ⟨_, hsa.1⟩
    exact hsa.unique hu₁ ▸ hu₂

open StarOrderedRing
lemma _root_.IsLUB.conjugate_star_right_of_isUnit' {R : Type*} [Ring R]
      [StarRing R] [PartialOrder R] [StarOrderedRing R] {s : Set R} {x : R}
      (h : IsLUB s x) (r : R) (hr : IsUnit r) :
    IsLUB (conjOrderHom r '' s) (r * x * star r) := by
  lift r to Rˣ using hr
  exact (conjUnitsOrderIso r).isLUB_image'.mpr h

open Filter
lemma IsLUB.conjugate_star_right (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (hbd : BddAbove s)
    (h : IsLUB s u) : IsLUB (conjOrderHom a '' s) (a * u * star a) := by
  have hd' : DirectedOn (· ≤ ·) (conjOrderHom a '' s) :=
    RelHomClass.directedOn hd
  have hnon' : (conjOrderHom a '' s).Nonempty := hnon.image _
  have hbd' : BddAbove (conjOrderHom a '' s) := (conjOrderHom a).monotone.map_bddAbove hbd
  have isLUB := hd'.isLUB_csSup hnon' hbd'
  have := tendsto_atTop_isLUB (Subtype.mono_coe (conjOrderHom a '' s))
    (Subtype.range_coe (s := conjOrderHom a '' s) ▸ isLUB)
  simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq] at this
  have hnon'' := hnon'.to_subtype
  have hd'' := directedOn_iff_isDirectedOrder.mp hd'
  have neBot : (atTop : Filter (conjOrderHom a '' s)).NeBot := atTop_neBot
  convert isLUB
  refine tendsto_nhds_unique ?_ this

  sorry

-- on master this is about `Subtype t` ... gross.
theorem _root_.Subtype.mono_coe' {α : Type*} [Preorder α] (t : Set α) : Monotone ((↑) : t → α) :=
  fun _ _ ↦ id

open Topology
lemma foo (a u : σ(M, P)) (s : Set σ(M, P))
    (hd : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) (hbd : BddAbove s)
    (h : IsLUB s u) : IsLUB (conjOrderHom a '' s) (a * u * star a) := by
  have : Nonempty s := hnon.to_subtype
  have : IsDirectedOrder s := directedOn_iff_isDirectedOrder.mp hd
  have h₁ : Tendsto (· : s → σ(M, P)) atTop (𝓝 u) :=
    tendsto_atTop_isLUB (Subtype.mono_coe s) <| Subtype.range_coe ▸ h
  have h₂ (b : σ(M, P)) (hb : IsUnit b) :
      Tendsto (fun x : s ↦ b * x * star b) atTop (𝓝 (b * u * star b)) := by
    refine tendsto_atTop_isLUB (conjOrderHom b |>.monotone.comp <| Subtype.mono_coe' s) ?_
    convert h.conjugate_star_right_of_isUnit' b hb
    ext
    simp
  suffices Tendsto (fun x : s ↦ a * x * star a) atTop (𝓝 (a * u * star a)) by
    convert isLUB_of_tendsto_atTop' (conjOrderHom a |>.monotone.comp <| Subtype.mono_coe' s) this
    ext
    simp

  sorry



end Ultraweak
