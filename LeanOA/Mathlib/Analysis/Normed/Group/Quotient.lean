module

public import Mathlib.Analysis.Normed.Group.Quotient

/-! # Bounds on functions out of a normed quotient

A bound `‖g m‖ ≤ C * ‖m‖` for a function `g` on `M ⧸ S`, checked along the quotient map, passes to
the quotient norm: `‖g x‖ ≤ C * ‖x‖` for all `x : M ⧸ S`.
-/

@[expose] public section

namespace QuotientGroup

variable {M N : Type*} [SeminormedCommGroup M] [Norm N] {S : Subgroup M}

/-- A bound on a function on `M ⧸ S` along the quotient map passes to the quotient norm. -/
@[to_additive
/-- A bound on a function on `M ⧸ S` along the quotient map passes to the quotient norm. -/]
lemma norm_apply_le_of_forall_mk {g : M ⧸ S → N} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ m : M, ‖g m‖ ≤ C * ‖m‖) (x : M ⧸ S) : ‖g x‖ ≤ C * ‖x‖ := by
  rcases hC.eq_or_lt with rfl | hC
  · obtain ⟨m, rfl⟩ := mk_surjective x
    simpa using h m
  · rw [← div_le_iff₀' hC, le_norm_iff]
    rintro m rfl
    exact (div_le_iff₀' hC).mpr (h m)

end QuotientGroup

namespace Submodule.Quotient

variable {R M N : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] [Norm N]
  {S : Submodule R M}

/-- A bound on a function on `M ⧸ S` along the quotient map passes to the quotient norm. -/
lemma norm_apply_le_of_forall_mk {g : M ⧸ S → N} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ m : M, ‖g (mk m)‖ ≤ C * ‖m‖) (x : M ⧸ S) : ‖g x‖ ≤ C * ‖x‖ :=
  QuotientAddGroup.norm_apply_le_of_forall_mk (S := S.toAddSubgroup) hC h x

end Submodule.Quotient
