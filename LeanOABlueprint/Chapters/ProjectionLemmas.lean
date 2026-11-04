import LeanOABlueprint.Base

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Projection Lemmas" =>

Let $`\mathcal{A}` be a unital $`C^*`-algebra in this chapter. Here we collect relevant
results about (self-adjoint) projections in $`\mathcal{A}`. Recall that an element $`p` in a
$`C^*`-algebra is a projection if $`p^2 = p^* = p`. By the Spectral Mapping Theorem (or using
the full Gelfand Duality), a self-adjoint element $`a \in \mathcal{A}` is a projection if and
only if the spectrum of $`a` is contained in $`\{0, 1\}`.

:::lemma_ "lem:proj_le_one" (tags := "mathlib") (lean := "IsStarProjection.le_one") (uses := "lem:selfadjoint_le_norm")
For all projections $`p \in \mathcal{A}`, $`p \le 1`.
:::

:::proof "lem:proj_le_one"
We can get this by Gelfand duality (cf. Sakai 1.2.3) and
{bpref "lem:selfadjoint_le_norm"}[].
:::

:::lemma_ "lem:proj_sub_pos_iff_comm_eq_self" (lean := "IsStarProjection.le_tfae") (uses := "lem:star_conj_pos, lem:proj_le_one")
Let $`\mathcal{A}` be a $`C^*`-algebra and $`p, q \in \mathcal{A}` be projections. Then
$`p - q \ge 0` if and only if $`qp = pq = q`.
:::

:::proof "lem:proj_sub_pos_iff_comm_eq_self"
By {bpref "lem:star_conj_pos"}[], if $`p - q \ge 0` then
$`q(p - q)q = qpq - q^3 = qpq - q \ge 0`. By {bpref "lem:proj_le_one"}[], we have $`p \le 1`,
and employing {bpref "lem:star_conj_pos"}[] we obtain $`qpq \le q1q = q`. Since
$`qpq \ge q` and $`qpq \le q` we have $`qpq = q`, which implies that $`q(p - q)q = 0`. By the
$`C^*`-property of the norm, we have $`\|(p - q)^{1/2} q\|^2 = \|q(p - q)q\| = 0` and so
$`(p - q)^{1/2} q = 0` and therefore $`(p - q)q = (p - q)^{1/2}(p - q)^{1/2} q = 0`. It
follows that $`pq = q`, and taking adjoints, $`qp = q`. Conversely, if $`qp = pq = q`, one
easily checks that $`p - q` is a projection, and so its spectrum is contained in
$`\{0, 1\}` and it is positive.
:::

:::corollary "cor:proj_sub_of_subproj" (lean := "IsStarProjection.le_tfae") (uses := "lem:proj_sub_pos_iff_comm_eq_self")
For all projections $`p, q \in \mathcal{A}` such that $`q \le p`, $`p - q` is a projection.
:::

The next result is specific to $`W^*`-algebras. Sakai obtains it from the fact that the
projections of a $`W^*`-algebra form a complete lattice
({bpref "prop:proj_compl_lat_wstar_Sak_1_10_2"}[], via the correspondence between
$`\sigma`-closed one-sided ideals and projections in
{bpref "prop:one_sided_ideals_in_wstar_proj_Sak_1_10_1"}[]). The proof of
{bpref "thm:sigma_cts_of_normal_Sak_1_13_2"}[] only needs suprema of directed sets, for which the
following direct argument suffices.

:::lemma_ "lem:directed_sup_proj" (lean := "Ultraweak.isStarProjection_of_isLUB") (uses := "lem:sigma_cont_of_normal_Sak_1_7_4, lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8, lem:pos_sa_sigma_closed_Sak_1_7_1")
In a $`W^*`-algebra $`M`, the supremum of a nonempty directed set of projections is a projection.
:::

:::proof "lem:directed_sup_proj"
Let $`e` be the supremum of the directed set $`(q_\alpha)` of projections; it is the
$`\sigma`-limit of the $`q_\alpha` by {bpref "lem:sigma_cont_of_normal_Sak_1_7_4"}[], hence is
self-adjoint by {bpref "lem:pos_sa_sigma_closed_Sak_1_7_1"}[]. Since $`q_\alpha \le e \le 1`, we
have $`0 \le q_\alpha (1 - e) q_\alpha \le q_\alpha (1 - q_\alpha) q_\alpha = 0`, and so
$`(1 - e) q_\alpha = 0` by the $`C^*`-identity, i.e., $`e q_\alpha = q_\alpha`. Multiplication is
separately $`\sigma`-continuous ({bpref "lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8"}[]), so
$`q_\alpha = e q_\alpha \to e^2`, but also $`q_\alpha \to e`. Hence $`e^2 = e`.
:::
