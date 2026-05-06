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

-- TODO: show that any `F ≃ₗ[𝕜] StrongDual 𝕜 E` yields an `IsCompatibleDual` instance.
lemma _root_.LinearEquiv.IsCompatibleDual (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (e : F ≃ₗ[𝕜] StrongDual 𝕜 E)
    (hB : B.flip = (ContinuousLinearMap.coeLM 𝕜).comp e.toLinearMap) :
    B.IsCompatibleDual :=
    ⟨by convert congr($(hB).range)
        simp, by simpa [hB] using e.injective⟩

/-- Intended to help handle the above TODO. -/
noncomputable def bilin_flip_range (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (hB : Function.Injective B.flip) : F ≃ₗ[𝕜] B.flip.range :=
  let φ := B.flip.rangeRestrict.toFun
  have hφ : Function.Injective φ := by simpa [φ] using hB
  let ψ := Classical.choose (Function.Injective.leftInverse φ hφ)
  have hψ : Function.LeftInverse ψ φ := by
    simpa [ψ, φ] using Classical.choose_spec
      (Function.Injective.leftInverse φ hφ)
  { toFun f := ⟨B.flip f, mem_range_self ..⟩,
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    invFun := ψ
    left_inv := hψ
    right_inv :=Function.RightInverse.leftInverse_of_surjective
       (Function.LeftInverse.rightInverse hψ) (by simp [Function.Surjective]) }

/-

I actually don't think that the above TODO is possible. The problem is that an
arbitrary identification `e : F ≃ₗ[𝕜] StrongDual 𝕜 E` doesn't seem to be able to guarantee
us that every element in the codomain will have the form `B(· , f)` for some `f : F`.

noncomputable def StrongDual_to_coeLM_range :
    StrongDual 𝕜 E ≃ₗ[𝕜] (ContinuousLinearMap.coeLM 𝕜 (M := E) (R := 𝕜) (N₃:= 𝕜)).range where
      toFun f := (ContinuousLinearMap.coeLM 𝕜).rangeRestrict.toFun f
      map_add' := by aesop
      map_smul' := by aesop
      invFun := by sorry --finish later if this indeed will work.
      left_inv := sorry
      right_inv := sorry

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (hB : Function.Injective B.flip) (e : F ≃ₗ[𝕜] StrongDual 𝕜 E)

#check (B.bilin_flip_range hB).symm ≪≫ₗ e ≪≫ₗ StrongDual_to_coeLM_range

open LinearEquiv in
lemma _root_.LinearEquiv.IsCompatibleDual' (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    (hB : Function.Injective B.flip) (e : F ≃ₗ[𝕜] StrongDual 𝕜 E) : B.IsCompatibleDual :=
      let φ := (B.bilin_flip_range hB).symm ≪≫ₗ e
      { range_eq_range := sorry
        injective := sorry }

-/

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
