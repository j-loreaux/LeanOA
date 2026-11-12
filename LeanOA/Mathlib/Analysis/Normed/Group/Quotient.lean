module

public import Mathlib.Analysis.Normed.Group.Quotient

@[expose] public section

open Metric Set

namespace QuotientGroup

variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M}

@[to_additive]
lemma image_mk_ball (m : M) (r : ℝ) : ((↑) '' ball m r : Set (M ⧸ S)) = ball (m : M ⧸ S) r := by
  refine Set.ext <| mk_surjective.forall.2 fun x ↦ ?_
  simp only [mem_image, mem_ball, dist_eq_norm_div, ← mk_div, norm_lt_iff]
  apply (Equiv.divRight m).exists_congr
  simp [mk_div, and_comm]

end QuotientGroup

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] (S : Submodule R M)

lemma image_mk_ball (m : M) (r : ℝ) :
    (mk '' ball m r : Set (M ⧸ S)) = ball (mk m) r :=
  QuotientAddGroup.image_mk_ball (S := S.toAddSubgroup) m r

end Submodule.Quotient
