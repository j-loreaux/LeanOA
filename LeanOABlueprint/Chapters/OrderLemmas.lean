import LeanOABlueprint.Base

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Order Lemmas" =>

Let $`\mathcal{A}` be a unital $`C^*`-algebra in this chapter. We collect lemmas for the
ordering of elements in $`\mathcal{A}`. Recall that a self-adjoint element
$`a \in \mathcal{A}` is said to be *positive* if its spectrum is contained in
$`\mathbb{R}_{\ge 0}`. This is written $`a \ge 0`. If $`a, b \in \mathcal{A}` are
self-adjoint then $`b \le a` if $`b - a \ge 0`.

:::lemma_ "lem:pos_iff_star_mul_self_Sak_1_4_4" (lean := "CStarAlgebra.nonneg_TFAE, StarOrderedRing.nonneg_iff")
(Sakai 1.4.4) Let $`h \in \mathcal{A}`. The following are equivalent:

1. $`h \ge 0`;
2. there exists $`x \in \mathcal{A}` such that $`h = x^* x`.
:::

:::corollary "lem:star_conj_pos" (tags := "mathlib") (lean := "star_left_conjugate_nonneg") (uses := "lem:pos_iff_star_mul_self_Sak_1_4_4")
If $`h, a \in \mathcal{A}` with $`h \ge 0` then $`a^* h a \ge 0`.
:::

:::proof "lem:star_conj_pos"
By {bpref "lem:pos_iff_star_mul_self_Sak_1_4_4"}[],
$`a^* h a = a^* x^* x a = (xa)^* (xa) \ge 0`.
:::

:::lemma_ "lem:selfadjoint_le_norm" (tags := "mathlib") (lean := "IsSelfAdjoint.le_algebraMap_norm_self")
If $`x \in \mathcal{A}` is self-adjoint then $`\|x\| 1 - x \ge 0`.
:::
