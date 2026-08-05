/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Complexification of inner product spaces

In this file we define the complexification of an inner product space. So we can essentially
extend a `𝕜`-space `E` to a `ℂ`-space `E × E`, and extend operators to its complexification
in order to use `ℂ`-results. We (informally) think of `(x, y) : Complexification 𝕜 E` as
`x + I • y`.

In particular, `ℂ`-scalar multiplication is given by
`α • (x, y) = (ℜ α • x - ℑ α • y, ℜ α • y + ℑ α • x)`
and the `ℂ`-inner product is given by
`⟪(x, y), (z, w)⟫_ℂ = ℜ ⟪x, z⟫_𝕜 + ℜ ⟪y, w⟫_𝕜 + (ℜ (⟪x, w⟫_𝕜 - ⟪y, z⟫_𝕜)) * I`.

* `ContinuousLinearMap.toComplexification`: The complexification of an operator `T`, which is
  defined as `x ↦ (T x.re, T x.im)`.

-/

public section

open scoped InnerProductSpace

set_option linter.unusedVariables false in
/-- The complexification of an inner product space.
This is a type synonym of `WithLp 2 (E × E)`. -/
@[expose, nolint unusedArguments] def Complexification (𝕜 E : Type*) : Type _ := WithLp 2 (E × E)

variable {𝕜 E : Type*}

noncomputable instance [NormedAddCommGroup E] : NormedAddCommGroup (Complexification 𝕜 E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [NormedAddCommGroup E] [CompleteSpace E] : CompleteSpace (Complexification 𝕜 E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

namespace Complexification

/-- The real part of the complexification (the first component of the complexification). -/
@[expose] protected def re (v : Complexification 𝕜 E) : E := WithLp.fst v

/-- The imaginary part of the complexification (the second component of the complexification). -/
@[expose] protected def im (v : Complexification 𝕜 E) : E := WithLp.snd v

/-- Converting real and imaginary parts to the complexification. -/
@[expose] def mk (𝕜 : Type*) (x y : E) : Complexification 𝕜 E := WithLp.toLp 2 (x, y)

@[simp] lemma re_mk (x y : E) : (mk 𝕜 x y).re = x := rfl
@[simp] lemma im_mk (x y : E) : (mk 𝕜 x y).im = y := rfl
@[simp] lemma mk_re_im (v : Complexification 𝕜 E) : mk 𝕜 v.re v.im = v := rfl

@[ext] lemma ext {v w : Complexification 𝕜 E} (h₁ : v.re = w.re) (h₂ : v.im = w.im) : v = w := by
  rw [← mk_re_im v, ← mk_re_im w, h₁, h₂]

variable [NormedAddCommGroup E]

@[simp] lemma re_zero : (0 : Complexification 𝕜 E).re = 0 := rfl
@[simp] lemma im_zero : (0 : Complexification 𝕜 E).im = 0 := rfl
@[simp] lemma re_add (v w : Complexification 𝕜 E) : (v + w).re = v.re + w.re := rfl
@[simp] lemma im_add (v w : Complexification 𝕜 E) : (v + w).im = v.im + w.im := rfl
@[simp] lemma re_sub (v w : Complexification 𝕜 E) : (v - w).re = v.re - w.re := rfl
@[simp] lemma im_sub (v w : Complexification 𝕜 E) : (v - w).im = v.im - w.im := rfl
@[simp] lemma re_neg (v : Complexification 𝕜 E) : (-v).re = -v.re := rfl
@[simp] lemma im_neg (v : Complexification 𝕜 E) : (-v).im = -v.im := rfl
@[simp] lemma mk_zero_zero : mk 𝕜 (0 : E) 0 = 0 := rfl
@[simp] lemma neg_mk (x y : E) : -mk 𝕜 x y = mk 𝕜 (-x) (-y) := by ext <;> simp

@[simp] lemma mk_add_mk (x y z w : E) : mk 𝕜 x y + mk 𝕜 z w = mk 𝕜 (x + z) (y + w) := by
  ext <;> simp
@[simp] lemma mk_sub_mk (x y z w : E) : mk 𝕜 x y - mk 𝕜 z w = mk 𝕜 (x - z) (y - w) := by
  simp [sub_eq_add_neg]

lemma norm_sq_eq (v : Complexification 𝕜 E) : ‖v‖ ^ 2 = ‖v.re‖ ^ 2 + ‖v.im‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 v
lemma norm_eq (v : Complexification 𝕜 E) : ‖v‖ = √(‖v.re‖ ^ 2 + ‖v.im‖ ^ 2) :=
  WithLp.prod_norm_eq_of_L2 v

@[simp] lemma norm_mk_zero_right (x : E) : ‖mk 𝕜 x 0‖ = ‖x‖ := by simp [norm_eq]
@[simp] lemma norm_mk_zero_left (x : E) : ‖mk 𝕜 0 x‖ = ‖x‖ := by simp [norm_eq]

lemma norm_re_le (x : Complexification 𝕜 E) : ‖x.re‖ ≤ ‖x‖ := by
  rw [norm_eq, Real.le_sqrt (norm_nonneg _) (by positivity)]
  simp

lemma norm_im_le (x : Complexification 𝕜 E) : ‖x.im‖ ≤ ‖x‖ := by
  rw [norm_eq, Real.le_sqrt (norm_nonneg _) (by positivity)]
  simp

lemma lipschitzWith_re : LipschitzWith 1 (Complexification.re (𝕜 := 𝕜) (E := E)) :=
  .of_dist_le_mul fun v w ↦ by simpa [dist_eq_norm] using norm_re_le (v - w)
lemma lipschitzWith_im : LipschitzWith 1 (Complexification.im (𝕜 := 𝕜) (E := E)) :=
  .of_dist_le_mul fun v w ↦ by simpa [dist_eq_norm] using norm_im_le (v - w)

@[fun_prop] lemma continuous_re : Continuous (Complexification.re (𝕜 := 𝕜) (E := E)) :=
  lipschitzWith_re.continuous
@[fun_prop] lemma continuous_im : Continuous (Complexification.im (𝕜 := 𝕜) (E := E)) :=
  lipschitzWith_im.continuous

lemma isometry_mk_zero_right : Isometry (mk 𝕜 · (0 : E)) :=
  .of_dist_eq fun x y ↦ by simp [dist_eq_norm]
lemma isometry_mk_zero_left : Isometry (mk 𝕜 (0 : E) ·) :=
  .of_dist_eq fun x y ↦ by simp [dist_eq_norm]

@[fun_prop] lemma continuous_mk_zero_right : Continuous (mk 𝕜 · (0 : E)) :=
  isometry_mk_zero_right.continuous
@[fun_prop] lemma continuous_mk_zero_left : Continuous (mk 𝕜 (0 : E) ·) :=
  isometry_mk_zero_left.continuous
@[fun_prop] lemma continuous_mk : Continuous fun p : E × E ↦ mk 𝕜 p.1 p.2 := by
  conv in mk 𝕜 _ _ => rw [show mk 𝕜 p.1 p.2 = mk 𝕜 p.1 0 + mk 𝕜 0 p.2 by simp]
  fun_prop

variable [RCLike 𝕜] [InnerProductSpace 𝕜 E]

instance : SMul ℂ (Complexification 𝕜 E) where
  smul z v := .mk 𝕜 ((z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im) ((z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im)

lemma smul_def (z : ℂ) (v : Complexification 𝕜 E) :
    z • v = .mk 𝕜 ((z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im) ((z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im) :=
  rfl

@[simp] lemma re_smul (z : ℂ) (v : Complexification 𝕜 E) :
    (z • v).re = (z.re : 𝕜) • v.re - (z.im : 𝕜) • v.im := rfl
@[simp] lemma im_smul (z : ℂ) (v : Complexification 𝕜 E) :
    (z • v).im = (z.im : 𝕜) • v.re + (z.re : 𝕜) • v.im := rfl

instance : Module ℂ (Complexification 𝕜 E) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp <;> module
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp <;> grind
  add_smul _ _ _ := by ext <;> simp <;> module
  zero_smul _ := by ext <;> simp

@[simp] lemma re_real_smul (r : ℝ) (v : Complexification 𝕜 E) : (r • v).re = (r : 𝕜) • v.re := by
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ) r, -Complex.coe_smul]

@[simp] lemma im_real_smul (r : ℝ) (v : Complexification 𝕜 E) : (r • v).im = (r : 𝕜) • v.im := by
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ) r, -Complex.coe_smul]

@[simp] lemma I_smul (v : Complexification 𝕜 E) : Complex.I • v = mk 𝕜 (-v.im) v.re := by
  ext <;> simp

/-- `(x, y) = (x, 0) + I • (y, 0)`. -/
lemma mk_eq_add_I_smul (x y : E) : mk 𝕜 x y = mk 𝕜 x 0 + Complex.I • mk 𝕜 y 0 := by simp

lemma norm_smul_eq (z : ℂ) (v : Complexification 𝕜 E) : ‖z • v‖ = ‖z‖ * ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
  simp [mul_pow, norm_sq_eq, Complex.sq_norm, Complex.normSq_apply,
    -inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_re_symm v.im v.re]
  grind

instance : NormedSpace ℂ (Complexification 𝕜 E) where norm_smul_le z v := (norm_smul_eq z v).le

noncomputable instance : Inner ℂ (Complexification 𝕜 E) where
  inner v w := ⟨RCLike.re (⟪v.re, w.re⟫_𝕜 + ⟪v.im, w.im⟫_𝕜),
    RCLike.re (⟪v.re, w.im⟫_𝕜 - ⟪v.im, w.re⟫_𝕜)⟩

@[simp] lemma re_inner (v w : Complexification 𝕜 E) :
    (⟪v, w⟫_ℂ).re = RCLike.re (⟪v.re, w.re⟫_𝕜 + ⟪v.im, w.im⟫_𝕜) := rfl
@[simp] lemma im_inner (v w : Complexification 𝕜 E) :
    (⟪v, w⟫_ℂ).im = RCLike.re (⟪v.re, w.im⟫_𝕜 - ⟪v.im, w.re⟫_𝕜) := rfl

noncomputable instance : InnerProductSpace ℂ (Complexification 𝕜 E) where
  norm_sq_eq_re_inner v := by simp [norm_sq_eq, RCLike.re_to_complex]
  conj_inner_symm _ _ := by simp [Complex.ext_iff, inner_re_symm]
  add_left _ _ _ := by simp [Complex.ext_iff, inner_add_left]; grind
  smul_left _ _ _ := by
    simp [Complex.ext_iff, inner_sub_left, inner_add_left, inner_smul_left]; grind

variable (𝕜 E) in
/-- conjugation -/
@[expose, simps apply] def conj : Complexification 𝕜 E ≃ₗᵢ⋆[ℂ] Complexification 𝕜 E where
  toFun v := .mk 𝕜 v.re (-v.im)
  invFun v := .mk 𝕜 v.re (-v.im)
  map_add' := by simp [add_comm]
  map_smul' _ _ := by ext <;> simp [RCLike.algebraMap_eq_ofReal, add_comm]
  norm_map' := by simp [norm_eq]
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma symm_conj : (conj 𝕜 E).symm = conj 𝕜 E := rfl

@[simp] lemma inner_conj_conj (x y) : inner ℂ (conj 𝕜 E x) (conj 𝕜 E y) = inner ℂ y x := by
  simp [Complex.ext_iff, inner_re_symm, sub_eq_add_neg, add_comm]

@[simp] lemma conj_eq_self_iff (x) : conj 𝕜 E x = x ↔ x.im = 0 := by
  simp only [conj_apply, Complexification.ext_iff, re_mk, im_mk, true_and]
  rw [eq_comm, ← sub_eq_zero]
  simp [← two_smul 𝕜]

/-- The complexification of `ℝ` is equivalent to `ℂ`. -/
example : Complexification ℝ ℝ ≃ₗᵢ[ℂ] ℂ where
  toFun x := x.re + x.im * Complex.I
  invFun x := .mk ℝ x.re x.im
  map_add' _ _ := by simp [add_mul]; grind
  map_smul' z _ := by
    rw [← Complex.re_add_im z]
    simp [add_mul, mul_add, -Complex.re_add_im, mul_mul_mul_comm _ Complex.I]
    grind
  norm_map' := by simp [norm_eq, Complex.norm_def, Complex.normSq, sq]
  left_inv _ := by simp
  right_inv _ := by simp

@[expose]
def _root_.Submodule.complexification (K : Submodule 𝕜 E) : Submodule ℂ (Complexification 𝕜 E) where
  carrier := {v | v.re ∈ K } ∩ { v | v.im ∈ K}
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' := by aesop

@[simp] lemma _root_.Submodule.mem_complexification {K : Submodule 𝕜 E} (x : Complexification 𝕜 E) :
    x ∈ K.complexification ↔ x.re ∈ K ∧ x.im ∈ K := by simp [Submodule.complexification]

end Complexification

namespace ContinuousLinearMap
variable {F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open Complexification

/-- Complexification of a continuous linear map between inner product spaces. -/
@[expose, simps] noncomputable def toComplexification (T : E →L[𝕜] F) :
    Complexification 𝕜 E →L[ℂ] Complexification 𝕜 F where
  toFun v := .mk 𝕜 (T v.re) (T v.im)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp] lemma toComplexification_zero : (0 : E →L[𝕜] F).toComplexification = 0 := by ext <;> simp

@[simp] lemma toComplexification_add (S T : E →L[𝕜] F) :
    (S + T).toComplexification = S.toComplexification + T.toComplexification := by ext <;> simp

@[simp] lemma toComplexification_sub (S T : E →L[𝕜] F) :
    (S - T).toComplexification = S.toComplexification - T.toComplexification := by ext <;> simp

@[simp] lemma toComplexification_neg (T : E →L[𝕜] F) :
    (-T).toComplexification = -T.toComplexification := by ext <;> simp

@[simp] lemma toComplexification_id :
    (ContinuousLinearMap.id 𝕜 E).toComplexification = .id ℂ (Complexification 𝕜 E) := by
  ext <;> simp

@[simp] lemma toComplexification_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (S.comp T).toComplexification = S.toComplexification.comp T.toComplexification := by
  ext <;> simp

@[simp] lemma toComplexification_one : (1 : E →L[𝕜] E).toComplexification = 1 := by ext <;> simp

@[simp] lemma toComplexification_mul (S T : E →L[𝕜] E) :
    (S * T).toComplexification = S.toComplexification * T.toComplexification := by simp [mul_def]

@[simp] lemma norm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖ = ‖T‖ := by
  refine le_antisymm ((opNorm_le_iff (norm_nonneg _)).mpr fun _ ↦ ?_) ?_
  · refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    simp only [mul_pow, norm_sq_eq, mul_add, toComplexification_apply, re_mk, im_mk]
    grw [T.le_opNorm, T.le_opNorm]
    simp [mul_pow]
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using T.toComplexification.le_opNorm (.mk 𝕜 x 0)

@[simp] lemma nnnorm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖₊ = ‖T‖₊ := by
  ext; simp
@[simp] lemma enorm_toComplexification (T : E →L[𝕜] F) : ‖T.toComplexification‖ₑ = ‖T‖ₑ := by
  simp [enorm_eq_nnnorm]

lemma toComplexification_injective :
    Function.Injective (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) := fun S T h ↦ by
  ext x; simpa using congr(($h (.mk 𝕜 x 0)).re)

@[simp] lemma toComplexification_inj {S T : E →L[𝕜] F} :
    S.toComplexification = T.toComplexification ↔ S = T :=
  toComplexification_injective.eq_iff

@[simp] lemma isIdempotentElem_toComplexification_iff {S : E →L[𝕜] E} :
    IsIdempotentElem S.toComplexification ↔ IsIdempotentElem S := by
  simp [IsIdempotentElem, ← toComplexification_mul]

alias ⟨_, _root_.IsIdempotentElem.toComplexification⟩ := isIdempotentElem_toComplexification_iff

@[simp] lemma injective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Injective T.toComplexification ↔ Function.Injective T := by
  refine ⟨fun h x y hxy ↦ ?_, fun h x y hxy ↦ ?_⟩
  · simpa using congr(($(h (a₁ := .mk 𝕜 x 0) (a₂ := .mk 𝕜 y 0)
      (by ext <;> simp [hxy]))).re)
  · have := by simpa [h.eq_iff] using congr(($hxy).re)
    have := by simpa [h.eq_iff] using congr(($hxy).im)
    simp_all [Complexification.ext_iff]

@[simp] lemma surjective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Surjective T.toComplexification ↔ Function.Surjective T := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨v, hv⟩ := h (.mk 𝕜 x 0)
    exact ⟨v.re, by simpa using congr(($hv).re)⟩
  · obtain ⟨v, hv⟩ := h x.re
    obtain ⟨w, hw⟩ := h x.im
    exact ⟨.mk 𝕜 v w, by simp [hv, hw]⟩

@[simp] lemma bijective_toComplexification_iff {T : E →L[𝕜] F} :
    Function.Bijective T.toComplexification ↔ Function.Bijective T := by
  simp [Function.Bijective]

lemma isometry_toComplexification : Isometry (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  .of_dist_eq <| by simp [dist_eq_norm, ← toComplexification_sub]

@[fun_prop] lemma continuous_toComplexification :
    Continuous (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  isometry_toComplexification.continuous

lemma lipschitzWith_toComplexification :
    LipschitzWith 1 (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  isometry_toComplexification.lipschitz

lemma isClosedEmbedding_toComplexification [CompleteSpace F] :
    Topology.IsClosedEmbedding (toComplexification (𝕜 := 𝕜) (E := E) (F := F)) :=
  isometry_toComplexification.isClosedEmbedding

@[simp] lemma ker_toComplexification (T : E →L[𝕜] F) :
    T.toComplexification.ker = T.ker.complexification := by
  ext; simp [Complexification.ext_iff]

@[simp] lemma range_toComplexification (T : E →L[𝕜] F) :
   T.toComplexification.range = T.range.complexification := by
  ext x
  simp only [LinearMap.mem_range, coe_coe, toComplexification_apply, Complexification.ext_iff,
    re_mk, im_mk, Submodule.complexification, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, ?_⟩
  · simp [← hy.1, ← hy.2]
  simp only [and_imp, forall_exists_index]
  exact fun y hy z hz ↦ ⟨.mk 𝕜 y z, by simp [hy, hz]⟩

-- move earlier (maybe remove ... hmmm)
lemma _root_.Submodule.mem_orthogonal_iff_re_inner_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) (y : E) :
    y ∈ Kᗮ ↔ ∀ u ∈ K, RCLike.re ⟪u, y⟫_𝕜 = 0 := by
  simp only [Submodule.mem_orthogonal]
  refine ⟨fun hy u hu ↦ by simp_all, fun h u hu ↦ ?_⟩
  simpa [inner_smul_left, RCLike.conj_mul, -inner_conj_symm] using
    h (⟪u, y⟫_𝕜 • u) (K.smul_mem _ hu)

@[simp] lemma _root_.Submodule.orthogonal_complexification (K : Submodule 𝕜 E) :
    K.complexificationᗮ = Kᗮ.complexification := by
  ext v
  simp only [Submodule.mem_complexification, Submodule.mem_orthogonal_iff_re_inner_eq_zero, and_imp]
  refine ⟨fun h ↦ ⟨fun u hu ↦ ?_, fun u hu ↦ ?_⟩, by aesop (add simp [Complex.ext_iff])⟩
  · simpa using h (.mk 𝕜 u 0) (by simpa)
  · simpa using h (.mk 𝕜 0 u) (by simp) (by simpa)

instance (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K.complexification.HasOrthogonalProjection where
  exists_orthogonal v :=
    have ⟨a, ha, hva⟩ := ‹K.HasOrthogonalProjection›.exists_orthogonal v.re
    have ⟨b, hb, hvb⟩ := ‹K.HasOrthogonalProjection›.exists_orthogonal v.im
    ⟨.mk 𝕜 a b, by simp [ha, hb], by simp [hva, hvb]⟩

-- or the other way around?
@[simp] lemma _root_.Submodule.toComplexification_starProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    K.starProjection.toComplexification = K.complexification.starProjection := by
  ext1 v
  refine (K.complexification.eq_starProjection_of_mem_of_inner_eq_zero (by simp) ?_).symm
  intro w hw
  have : v - K.starProjection.toComplexification v ∈ K.complexificationᗮ := by simp
  simp [-toComplexification_apply, inner_eq_zero_symm (y := w), this _ hw]

variable [CompleteSpace E] [CompleteSpace F]

@[simp] lemma adjoint_toComplexification (T : E →L[𝕜] F) :
    adjoint T.toComplexification = (adjoint T).toComplexification := by
  simp [eq_comm, eq_adjoint_iff, Complex.ext_iff, adjoint_inner_left]

@[simp] lemma star_toComplexification (T : E →L[𝕜] E) :
    star T.toComplexification = (star T).toComplexification :=
  adjoint_toComplexification T

@[simp] lemma isSelfAdjoint_toComplexification_iff {T : E →L[𝕜] E} :
    IsSelfAdjoint T.toComplexification ↔ IsSelfAdjoint T := by simp [isSelfAdjoint_iff]

alias ⟨_, _root_.IsSelfAdjoint.toComplexification⟩ := isSelfAdjoint_toComplexification_iff

@[simp] lemma isStarNormal_toComplexification_iff {T : E →L[𝕜] E} :
    IsStarNormal T.toComplexification ↔ IsStarNormal T := by
  simp [isStarNormal_iff, commute_iff_eq, ← toComplexification_mul]

alias ⟨_, _root_.IsStarNormal.toComplexification⟩ := isStarNormal_toComplexification_iff

@[simp] lemma isStarProjection_toComplexification_iff {T : E →L[𝕜] E} :
    IsStarProjection T.toComplexification ↔ IsStarProjection T := by
  simp [isStarProjection_iff]

@[simp] lemma isUnit_toComplexification_iff {T : E →L[𝕜] E} :
    IsUnit T.toComplexification ↔ IsUnit T := by simp [isUnit_iff_bijective]

@[simp] lemma spectrum_toComplexification (T : E →L[𝕜] E) :
    spectrum ℝ T.toComplexification = algebraMap ℝ 𝕜 ⁻¹' spectrum 𝕜 T := by
  ext r
  simp only [spectrum.mem_iff, Set.mem_preimage, not_iff_not]
  conv_rhs => rw [← isUnit_toComplexification_iff]
  congr! 1
  simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.ext_iff, Complexification.ext_iff]

protected lemma IsSelfAdjoint.norm_add_eq_max {S T : E →L[𝕜] E}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (h : S * T = 0) :
    ‖S + T‖ = max ‖S‖ ‖T‖ := by
  rw [← norm_toComplexification (S + T), toComplexification_add,
    hS.toComplexification.norm_add_eq_max hT.toComplexification
      (by simp [← toComplexification_mul, h])]
  simp

end ContinuousLinearMap

open ContinuousLinearMap Complexification
-- golfs of current results using complexification

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

-- golf of `ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`:
lemma ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal' {T : E →L[𝕜] E}
    (hT : IsIdempotentElem T) : IsSelfAdjoint T ↔ IsStarNormal T := by
  rw [← isSelfAdjoint_toComplexification_iff, ← isStarNormal_toComplexification_iff,
    hT.toComplexification.isSelfAdjoint_iff_isStarNormal]

-- golf of `ContinuousLinearMap.spectralRadius_eq_nnnorm`:
lemma ContinuousLinearMap.spectralRadius_eq_nnnorm' {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  nontriviality E
  refine le_antisymm (spectrum.spectralRadius_le_nnnorm T) ?_
  rw [← nnnorm_toComplexification, ← hT.toComplexification.spectralRadius_eq_nnnorm,
    ← hT.toComplexification.spectrumRestricts.spectralRadius_eq]
  simp only [spectralRadius, spectrum_toComplexification, Set.mem_preimage, iSup₂_le_iff]
  exact fun r hr ↦ le_iSup₂_of_le (algebraMap ℝ 𝕜 r) hr (by simp)

lemma ContinuousLinearMap.spectralRadius_toComplexification {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) : spectralRadius ℂ T.toComplexification = spectralRadius 𝕜 T := by
  simp [hT.toComplexification.spectralRadius_eq_nnnorm, spectralRadius_eq_nnnorm' hT]
