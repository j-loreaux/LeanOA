import LeanOA.Mathlib.Topology.Algebra.Module.WeakDual

namespace LinearMap

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

class IsCompatible (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop where
  range_eq_range : B.flip.range = (ContinuousLinearMap.coeLM 𝕜).range
  injective : Function.Injective B.flip

-- TODO: show that any `F ≃ₗ[𝕜] StrongDual 𝕜 E` yields an `IsCompatible` instance.

lemma IsCompatible.continuous (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible]
    (x : F) : Continuous (B.flip x) :=
  have ⟨y, hy⟩ := Submodule.ext_iff.mp h.range_eq_range (B.flip x) |>.mp (B.flip.mem_range_self x)
  hy ▸ y.continuous

noncomputable def IsCompatible.equiv (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible] :
    F ≃ₗ[𝕜] StrongDual 𝕜 E :=
  .ofBijective
    { toFun x := ⟨B.flip x, h.continuous B x⟩,
      map_add' _ _ := by ext; simp,
      map_smul' _ _ := by ext; simp }
    ⟨fun _ _ ↦ by simp [h.injective.eq_iff], fun x ↦
      have ⟨y, hy⟩ := h.range_eq_range ▸ LinearMap.mem_range_self _ x
      ⟨y, ContinuousLinearMap.ext fun _ ↦ congr($hy _)⟩⟩

@[simp]
lemma IsCompatible.equiv_apply_apply (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible] (y : F) (x : E) :
    h.equiv B y x = B x y := rfl

lemma IsCompatible.equiv_apply' (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible]
    (y : F) : h.equiv B y = ⟨B.flip y, h.continuous B y⟩ := rfl

noncomputable def IsCompatible.weakSpaceCLE (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible] :
    WeakBilin B ≃L[𝕜] WeakSpace 𝕜 E :=
  .trans
    (WeakBilin.congr _ (.refl _ _) h.equiv _ <| by ext x f; simp [← IsCompatible.equiv_apply_apply])
    WeakSpace.weakBilinCLE.symm

noncomputable def IsCompatible.weakDualCLE (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [h : B.IsCompatible] :
    WeakBilin B.flip ≃L[𝕜] WeakDual 𝕜 E :=
  .trans
    (WeakBilin.congr _ h.equiv (.refl 𝕜 E) _ <| by ext f x; simp [← IsCompatible.equiv_apply_apply])
    WeakDual.weakBilinCLE.symm

end

end LinearMap
