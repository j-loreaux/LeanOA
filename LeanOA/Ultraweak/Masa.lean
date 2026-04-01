import LeanOA.ExtremallyDisconnected
import LeanOA.Masa
import LeanOA.Ultraweak.LUB
import Mathlib.Algebra.Order.Monoid.Submonoid -- it makes no sense that this import is necessary
import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

section IsSelfAdjoint

variable {A : Type*} [NonUnitalRing A] [StarRing A]
  [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [ContinuousConstSMul ℝ A] [StarModule ℝ A] [ContinuousStar A] [T2Space A]

-- should we lower the priority here and make specialized instances for `NonUnitalStarSubalgebra`s
-- and `StarSubalgebra`s so that Lean doesn't have to hunt for the `SetLike` instances?
instance {S : Type*} [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℝ A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] :
    StarOrderedRing s := by
  refine .of_nonneg_iff' add_le_add_right fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · let r : A := CFC.sqrt (x : A)
    have hr : r ∈ s := by
      simp only [r, CFC.sqrt, cfcₙ_nnreal_eq_real _ (x : A) hx]
      exact cfcₙ_mem s _ x.1 x.2
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    simp [r, (CFC.sqrt_nonneg (x : A)).star_eq, CFC.sqrt_mul_sqrt_self (x : A)]
  · rintro ⟨x, rfl⟩
    exact star_mul_self_nonneg (x : A)

end IsSelfAdjoint

section IsStarNormal

variable {A : Type*} [NonUnitalRing A] [StarRing A]
  [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [ContinuousConstSMul ℂ A] [StarModule ℂ A] [ContinuousStar A] [T2Space A]

-- potentially we could just have an `IsROrC` instance, but I don't know how well that would work
-- given that we need to use `CFC.sqrt`.
-- should we lower the priority here and make specialized instances for `NonUnitalStarSubalgebra`s
-- and `StarSubalgebra`s so that Lean doesn't have to hunt for the `SetLike` instances?
instance {S : Type*} [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] :
    StarOrderedRing s := by
  have : SMulMemClass S ℝ A := ⟨fun r _ h ↦ SMulMemClass.smul_mem (r : ℂ) h⟩
  have : ContinuousConstSMul ℝ A :=
    Topology.IsInducing.id.continuousConstSMul Complex.ofReal (by simp)
  infer_instance

end IsStarNormal

section

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

open scoped Ultraweak

variable (M P) in
noncomputable abbrev WStarAlgebra.instCCPO : ConditionallyCompletePartialOrderSup M :=
  inferInstanceAs (ConditionallyCompletePartialOrderSup σ(M, P))

open WeakDual ContinuousMap
open scoped ComplexOrder

section Unitary

variable {R : Type*} [Monoid R] [StarMul R]

lemma Unitary.commute_self_star (u : unitary R) : Commute u (star u) := by simp [commute_iff_eq]
lemma Unitary.commute_star_self (u : unitary R) : Commute (star u) u := by simp [commute_iff_eq]

lemma commute_unitary_self_star {u : R} (hu : u ∈ unitary R) : Commute u (star u) := by
  simpa only [commute_iff_eq, Subtype.ext_iff, Submonoid.coe_mul, Unitary.coe_star] using
    Unitary.commute_self_star ⟨u, hu⟩

lemma commute_unitary_star_self {u : R} (hu : u ∈ unitary R) : Commute (star u) u :=
  commute_unitary_self_star hu |>.symm

lemma commute_unitary_iff_star_mul_mul {x : R} {u : unitary R} :
    Commute (u : R) x ↔ star u * x * u = x := by
  simpa using (Unitary.toUnits u).commute_iff_inv_mul_cancel

lemma commute_unitary_iff_star_mul_mul_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ star u * x * u = x :=
  commute_unitary_iff_star_mul_mul (u := ⟨u, hu⟩)

lemma commute_unitary_iff_mul_mul_star {x : R} {u : unitary R} :
    Commute (u : R) x ↔ u * x * star u = x := by
  simpa using (Unitary.toUnits u).commute_iff_mul_inv_cancel

lemma commute_unitary_iff_mul_mul_star_of_mem {x u : R} {hu : u ∈ unitary R} :
    Commute (u : R) x ↔ u * x * star u = x :=
  commute_unitary_iff_mul_mul_star (u := ⟨u, hu⟩)

end Unitary

section CommuteSpan

variable {R M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring M] [Module R M]
  [IsScalarTower R M M] [SMulCommClass R M M]

/-- If every element of a set `s` commutes with `x`, then every element of `Submodule.span R s`
commutes with `x`. -/
theorem Commute.span_left {s : Set M} {x : M} (h : ∀ y ∈ s, Commute y x) :
    ∀ y ∈ Submodule.span R s, Commute y x := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem _ _ => aesop
  | zero => exact Commute.zero_left _
  | add _ _ _ _ h₁ h₂ => exact h₁.add_left h₂
  | smul _ _ _ h => exact h.smul_left _

/-- If every element of a set `s` commutes with `x`, then every element of `Submodule.span R s`
commutes with `x`. -/
theorem Commute.span_right {s : Set M} {x : M} (h : ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Submodule.span R s, Commute x y := by
  simp only [Commute.symm_iff (a := x)] at *
  exact Commute.span_left h


end CommuteSpan

section StarMemClass

@[simp]
lemma Subtype.isSelfAdjoint_iff {S R : Type*} [Star R] [SetLike S R] [StarMemClass S R]
    {s : S} {x : s} : IsSelfAdjoint (x : R) ↔ IsSelfAdjoint x := by
  simp [IsSelfAdjoint, Subtype.ext_iff]

end StarMemClass

namespace StarSubalgebra

-- this should be an instance, but right now the hypothesis does not involve `WStarAlgebra` and
-- instead uses `Ultraweak`. Thus Lean can't find the synthesization order because it doesn't
-- know how to choose `P`. Maybe we leave this version as a lemma?
set_option backward.isDefEq.respectTransparency false in
include P in
open Submodule StarOrderedRing in
open scoped ComplexOrder IsMulCommutative in
lemma IsMasa.extremallyDisconnected_characterSpace (S : StarSubalgebra ℂ M) [hS : S.IsMasa] :
    ExtremallyDisconnected (characterSpace ℂ S) := by
  /- Since `M` has a predual, it is a conditionally complete partial order.
  To show that `characterSpace ℂ S` is extremally disconnected, it suffices to prove that
  `C(characterSpace ℂ S, ℝ)` is monotone complete. Note that using `ℝ` instead of `ℂ` here is
  essential for the proof technique. So take a nonempty directed set `s` in
  `C(characterSpace ℂ S, ℝ)` which is bounded above; we will show it has a supremum.

  The Gelfand transform is a star algebra isomorphism (`e`)
  and an order isomorphism (`o`) between `S` and `C(characterSpace ℂ S, ℂ)`.
  We let `f` denote the composition of the maps
  `C(characterSpace ℂ S, ℝ) → C(characterSpace ℂ S, ℂ) → S → M`, which is monotone (and a
  star algebra homomorphism). As such the image `f '' s` is directed and bounded above.
  Since `M` is monotone complete, this set has a supremum `u`, which is selfadjoint because
  the elements of `f '' s` are. -/
  let _ := WStarAlgebra.instCCPO M P
  refine .ofConditionallyCompletePartialOrderSupContinuousMap
    (𝕜 := ℝ) fun s hs hnon hbdd ↦ ?_
  let e := gelfandStarTransform S
  let o : S ≃o C(characterSpace ℂ S, ℂ) := OrderIsoClass.toOrderIso e
  let (eq := hf_eq) f : C(characterSpace ℂ S, ℝ) → M := Subtype.val ∘ o.symm ∘ realToRCLike ℂ
  have hf : Monotone f := fun _ _ ↦ by simp [f]
  replace hs : DirectedOn (· ≤ ·) (f '' s) := hs.mono_comp hf
  replace hbdd : BddAbove (f '' s) := hf.map_bddAbove hbdd
  let u := ⨆ i : s, f i
  have hu : IsLUB (f '' s) u := hs.isLUB_ciSup_set hbdd hnon
  have hu' : IsSelfAdjoint u := by
    refine .of_ge (hu.1 (hnon.image f).some_mem) ?_
    obtain ⟨g, hg, hg_eq⟩ := (hnon.image f).some_mem
    rw [← hg_eq]
    exact isSelfAdjoint_realToRCLike (𝕜 := ℂ) (f := g) |>.map e.symm |>.map S.subtype
  /- We will show that `u ∈ S` by showing that it commutes with all elements of `S`, which is
  sufficient because `u` is normal and `S` is a masa. Since the `S` is spanned by `unitary S`,
  it suffices to show that `u` commutes with all unitaries in `S`. -/
  have hu_mem : u ∈ S := by
    have hu'' : IsStarNormal u := hu'.isStarNormal
    refine IsMasa.mem_of_commute _ (x := u) ?_
    suffices ∀ v ∈ span ℂ (S.toSubmodule.subtype '' (unitary S : Set S)), Commute u v by
      simp only [← map_span] at this
      simpa [CStarAlgebra.span_unitary S]
    suffices ∀ v ∈ unitary S, Commute u v from Commute.span_right (by simpa)
    intro v hv
    /- So if `v ∈ S` is unitary, to show that `v` commutes with `u`, it suffices to show that
    `v * u * star v = u`. Now `v * u * star v` is the supremum of `v * (f '' s) * star v`, but
    this set coincides with `f '' s`, since the latter is a subset of `S` which is commutative.
    Thus `v * u * star v` coincides with the supremum of `f '' s`, which is `u`. -/
    lift v to unitary S using hv
    refine .symm <| (commute_unitary_iff_mul_mul_star
      (u := Unitary.map (⟨S.subtype.toRingHom, by simp⟩ : S →⋆* M) v) |>.mpr ?_)
    have h_image : conjOrderHom (v : M) '' (f '' s) = f '' s := by
      convert Set.image_id (f '' s) using 1
      apply Set.EqOn.image_eq
      rintro _ ⟨x, -, rfl⟩
      simp [f, ←MulMemClass.coe_mul, ←StarMemClass.coe_star, mul_comm (v : S), mul_assoc _ (v : S)]
    have := h_image ▸ (hu.conjugate_star_right_of_isUnit (v : M) <|
      (Unitary.toUnits v |>.map (SubmonoidClass.subtype S) |>.isUnit))
    exact this.unique hu
  /- Since `u ∈ S`, is the supremum of a set of elements in `S`, applying the Gelfand transform
  we obtain the supremum of a collection of elements in `C(characterSpace ℂ S, ℂ)`. But since
  `u` is selfadjoint, so also is its image under the Gelfand transform, so we may realize this image
  as an element of `C(characterSpace ℂ S, ℝ)`, thereby obtaining our desired supremum. -/
  lift u to S using hu_mem with u
  rw [hf_eq, Function.comp_def (f := Subtype.val), ← Set.image_image (g := Subtype.val)] at hu
  replace hu := hu.of_image (by simp)
  rw [Function.comp_def (f := o.symm), ← Set.image_image (g := o.symm), o.symm.isLUB_image,
    o.symm_symm] at hu
  have : IsSelfAdjoint (o u) := .map (by simpa using hu') e
  exact ⟨_, (this.realToRCLike_rclikeToReal ▸ hu).of_image <| by simp⟩

end StarSubalgebra

end
