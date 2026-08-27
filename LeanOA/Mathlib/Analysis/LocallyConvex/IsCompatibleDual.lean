module

public import LeanOA.Mathlib.Topology.Algebra.Module.WeakDual

@[expose] public section

namespace LinearMap

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

/-- A linear topology on `E` is compatible with the bilinear form `B` if the
every continuous linear functional on `E` has the form `B.flip f` for exactly one `f : F`. -/
class IsCompatibleDual (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  range_eq_range : B.flip.range = (ContinuousLinearMap.coeLM 𝕜).range
  injective : Function.Injective B.flip

open scoped ContinuousLinearMap in
@[simp]
lemma ContinuousLinearMap.coeLM_injective {R M N : Type*} (S : Type*) [Semiring R] [Semiring S]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [TopologicalSpace N] [AddCommMonoid N]
    [Module R N] [Module S N] [SMulCommClass R S N] [ContinuousConstSMul S N] [ContinuousAdd N] :
    Function.Injective (ContinuousLinearMap.coeLM S : (M →L[R] N) →ₗ[S] M →ₗ[R] N) := by
  simp [Function.Injective, DFunLike.ext_iff]

lemma _root_.LinearEquiv.IsCompatibleDual (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (e : F ≃ₗ[𝕜] StrongDual 𝕜 E)
    (hB : B.flip = (ContinuousLinearMap.coeLM 𝕜).comp e.toLinearMap) :
    B.IsCompatibleDual :=
    ⟨by convert congr($(hB).range)
        simp, by simpa [hB] using e.injective⟩

lemma IsCompatibleDual.continuous (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual]
    (x : F) : Continuous (B.flip x) :=
  have ⟨y, hy⟩ := Submodule.ext_iff.mp h.range_eq_range (B.flip x) |>.mp (B.flip.mem_range_self x)
  hy ▸ y.continuous

/-- Linear equivalence of `F` with `StrongDual 𝕜 E` obtained from `B.IsCompatibleDual`. -/
noncomputable def IsCompatibleDual.equiv (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual] :
    F ≃ₗ[𝕜] StrongDual 𝕜 E :=
  .ofBijective
    { toFun x := ⟨B.flip x, h.continuous B x⟩,
      map_add' _ _ := by ext; simp,
      map_smul' _ _ := by ext; simp }
    ⟨fun _ _ ↦ by simp [h.injective.eq_iff], fun x ↦
      have ⟨y, hy⟩ := h.range_eq_range ▸ LinearMap.mem_range_self _ x
      ⟨y, ContinuousLinearMap.ext fun _ ↦ congr($hy _)⟩⟩

@[simp]
lemma IsCompatibleDual.equiv_apply_apply (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual]
    (y : F) (x : E) :
  h.equiv B y x = B x y := rfl

lemma IsCompatibleDual.equiv_apply' (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual]
    (y : F) : h.equiv B y = ⟨B.flip y, h.continuous B y⟩ := rfl

/-- Continuous linear equivalence of `WeakBilin B` with `WeakSpace 𝕜 E` obtained from
  `B.IsCompatibleDual`. -/
noncomputable def IsCompatibleDual.weakSpaceCLE (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual] :
    WeakBilin B ≃L[𝕜] WeakSpace 𝕜 E :=
  .trans
    (WeakBilin.congr _ (.refl _ _) h.equiv _ <| by ext x f; simp
      [← IsCompatibleDual.equiv_apply_apply])
    WeakSpace.weakBilinCLE.symm

/-- Continuous linear equivalence of `WeakBilin B.flip` with `WeakDual 𝕜 E` obtained from
  `B.IsCompatibleDual`. -/
noncomputable def IsCompatibleDual.weakDualCLE (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatibleDual] :
    WeakBilin B.flip ≃L[𝕜] WeakDual 𝕜 E :=
  .trans
    (WeakBilin.congr _ h.equiv (.refl 𝕜 E) _ <| by ext f x; simp
      [← IsCompatibleDual.equiv_apply_apply])
    WeakDual.weakBilinCLE.symm

end

end LinearMap
