module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

public section

open scoped InnerProductSpace

lemma Submodule.mem_orthogonal_iff_re_inner_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) (y : E) :
    y ∈ Kᗮ ↔ ∀ u ∈ K, RCLike.re ⟪u, y⟫_𝕜 = 0 := by
  simp only [Submodule.mem_orthogonal]
  refine ⟨fun hy u hu ↦ by simp_all, fun h u hu ↦ ?_⟩
  simpa [inner_smul_left, RCLike.conj_mul, -inner_conj_symm] using
    h (⟪u, y⟫_𝕜 • u) (K.smul_mem _ hu)
