import LeanOABlueprint.Base

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Positive Linear Functionals and States" =>

Let $`M` be a $`W^*`-algebra and let $`T` denote the set of all $`\sigma`-continuous positive
linear functionals on $`M`, and $`E` the linear space of all finite linear combinations of
elements of $`T`. Let $`P` and $`M^s` denote the set of positive elements and the set of
self-adjoint elements of $`M`, respectively.

:::lemma_ "lem:pos_cvx_cone" (tags := "mathlib") (lean := "ConvexCone.positive")
$`P` is a convex cone in $`M`.
:::

:::lemma_ "lem:pos_sa_sigma_closed_Sak_1_7_1" (lean := "Ultraweak.isClosed_setOf_isSelfAdjoint, Ultraweak.isClosed_nonneg") (uses := "def:sigma_top")
(Sakai 1.7.1) $`P` and $`M^s` are $`\sigma`-closed.
:::

:::lemma_ "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2" (lean := "Ultraweak.exists_positiveCLM_apply_lt_zero") (uses := "def:sigma_top, lem:pos_cvx_cone, lem:pos_sa_sigma_closed_Sak_1_7_1")
(Sakai 1.7.2) For any self-adjoint element $`a \notin P`, there exists $`\varphi \in T` such
that $`\varphi(a) < 0`.
:::

:::proof "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2"
By {bpref "lem:pos_cvx_cone"}[] and {bpref "lem:pos_sa_sigma_closed_Sak_1_7_1"}[], $`P` is a
$`\sigma`-closed convex cone in the real locally convex space $`M^s`. By the Hahn-Banach
Separation Theorem, there is a $`\sigma`-continuous real linear functional $`g` on $`M^s`
such that $`\inf_{h \in P} g(h) > g(a)`. Since $`P` is a cone, if $`g(h) < 0` then we could
scale $`h` by a positive constant so that $`g(ch) \le g(a)`, which is nonsense. Therefore
$`g(h) \ge 0` for all $`h \ge 0`, and the infimum above must be zero (which can again be seen
by scaling). It follows that $`0 > g(a)`.

To appropriately extend $`g` to a functional on $`M`, define
$`\varphi(a + ib) = g(a) + i g(b)` for any $`a, b \in M^s`. This $`\varphi` is a (complex)
linear functional on $`M`, and the $`*`-operation is $`\sigma`-continuous because $`M^s` is
$`\sigma`-closed (by {bpref "lem:pos_sa_sigma_closed_Sak_1_7_1"}[]). It follows that
$`\varphi` is a $`\sigma`-continuous positive linear functional on $`M` such that
$`\varphi(a) = g(a) < 0`.
:::

:::lemma_ "lem:uw_pos_sep_pts" (lean := "Ultraweak.ext_positiveCLM") (uses := "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2, def:sigma_top")
If $`a \in M`, and $`\psi(a) = 0` for every $`\psi \in T`, then $`a = 0`.
:::

:::proof "lem:uw_pos_sep_pts"
Given nonzero $`a \in P` in $`M`, since $`P` is a cone, $`-a \notin P`. By
{bpref "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2"}[], there is a $`\varphi \in T` such
that $`\varphi(-a) < 0`, hence $`\varphi(a) > 0`. The desired statement follows by
contraposition.
:::
