import LeanOABlueprint.Base

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Normality and Ultraweak Continuity for Positive Functionals" =>

In what follows, let $`M` be a (nonzero) $`W^*`-algebra. Let $`\mathcal{P}(M)` denote the
projection lattice of $`M`. Let $`\varphi` be a positive linear functional on $`M`. We say
$`\varphi` is *normal* if whenever $`(p_\alpha)` is an increasing net of projections in $`M`
with supremum $`p`, we have $`\varphi(p_\alpha) \to \varphi(p)`. In this chapter we show that
this property is equivalent to $`\sigma(M, M_*)`-continuity. We say that a linear functional
$`\varphi` on $`M` is *positive* if $`\varphi(x) \ge 0` whenever $`x \ge 0`.

# Ultraweakly Continuous Implies Normal

In what follows, let $`T` denote the set of all $`\sigma`-continuous positive linear
functionals on $`M`, and $`E` the linear space of all finite linear combinations of elements
of $`T`. Let $`P` denote the set of positive elements of $`M`.

:::lemma_ "lem:homeo_of_cts_bij_cpt_haus" (tags := "mathlib") (lean := "isHomeomorph_iff_continuous_bijective")
Every continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
:::

:::lemma_ "lem:cauchy_schwarz" (tags := "mathlib") (lean := "PositiveLinearMap.norm_map_star_mul_le")
(Cauchy–Schwarz) If $`\varphi` is a positive linear functional on a $`C^*`-algebra, then
$`|\varphi(y^* x)|^2 \le \varphi(y^* y) \varphi(x^* x)` for all $`x, y`.
:::

:::lemma_ "lem:sigma_eq_weak_pos_on_bdd" (lean := "Ultraweak.cauchy_of_forall_posCLM_of_eventually, Ultraweak.tendsto_of_forall_posCLM_of_eventually, Ultraweak.continuousOn_of_forall_posCLM") (uses := "thm:Banach_Alaoglu, lem:homeo_of_cts_bij_cpt_haus, lem:uw_pos_sep_pts, def:sigma_top")
On bounded subsets of $`M`, the $`\sigma`-topology coincides with the weak topology
$`\sigma(M, E)` induced by the $`\sigma`-continuous positive linear functionals, and similarly
for the uniform structures. In particular, a bounded net in $`M` is $`\sigma`-Cauchy (resp.
$`\sigma`-convergent to $`x`) if and only if $`(\varphi(x_\lambda))` is Cauchy (resp. converges to
$`\varphi(x)`) for every $`\varphi \in T`.
:::

:::proof "lem:sigma_eq_weak_pos_on_bdd"
By {bpref "lem:uw_pos_sep_pts"}[] the subspace $`E` separates the points of $`M` and so
$`\sigma(M, E)` is Hausdorff. By the Banach-Alaoglu Theorem ({bpref "thm:Banach_Alaoglu"}[]) the
closed unit ball $`B` of $`M` is compact in the $`\sigma(M, M_*)`-topology. Since $`\sigma(M, E)`
is weaker than $`\sigma(M, M_*)`, the identity map on $`B` is
$`\sigma(M, M_*)`-$`\sigma(M, E)`-continuous, and therefore a homeomorphism, by
{bpref "lem:homeo_of_cts_bij_cpt_haus"}[]; as $`B` is compact, it is even a uniform equivalence.
The same holds for every closed ball, by scaling.
:::

:::theorem "lem:sigma_cont_of_normal_Sak_1_7_4" (lean := "Ultraweak.DirectedOn.exists_isLUB, Ultraweak.DirectedOn.isLUB_star_right_conjugate") (uses := "lem:sigma_eq_weak_pos_on_bdd, lem:non_pos_elem_neg_for_some_state_Sak_1_7_2, lem:star_conj_pos, lem:cauchy_schwarz, lem:selfadjoint_le_norm, def:sigma_top")
(Sakai 1.7.4) Every uniformly bounded, increasing net in $`M^s` converges to its least upper
bound in the $`\sigma`-topology. Further, if $`x = \sup_\lambda x_\lambda` then
$`a^* x a = \sup_\lambda a^* x_\lambda a`.
:::

:::proof "lem:sigma_cont_of_normal_Sak_1_7_4"
By {bpref "lem:sigma_eq_weak_pos_on_bdd"}[], to prove that a uniformly
bounded net $`(x_t)` is $`\sigma`-Cauchy, it is enough to check that for all
$`\varepsilon > 0` and $`\varphi \in T` there is a $`\Lambda` such that
$`\varphi(x_\lambda - x_\mu) \le \varepsilon` for $`\lambda \ge \mu \ge \Lambda`.

If $`(x_\lambda)` is a uniformly bounded increasing net in $`M^s`, and $`\varphi \in T`, then
$`(\varphi(x_\lambda))` is a uniformly bounded increasing net of real numbers and therefore
is Cauchy. By the above paragraph, $`(x_\lambda)` is $`\sigma`-Cauchy and by the
$`\sigma`-compactness of $`B` and the fact that $`(x_\lambda)` is increasing there exists
$`x \in B` so that $`x_\lambda \to x` in the $`\sigma`-topology. Since for any
$`\varphi \in T` and any $`\lambda` we have $`0 \le \varphi(x - x_\lambda)`, by
{bpref "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2"}[] we have $`0 \le x - x_\lambda`.
Therefore $`\sup(x_\lambda) \le x`. For a given $`\varphi \in T` and
$`\varepsilon = \varphi(x - \sup(x_\lambda))` one finds $`x_\lambda` so that
$`\varphi(x - x_\lambda) < \varphi(x - \sup(x_\lambda))`, which is a contradiction; therefore
$`x = \sup(x_\lambda)`.

By {bpref "lem:star_conj_pos"}[] and the fact that $`(u^{-1})^* = (u^*)^{-1}`, the relation
$`u^* x_\lambda u \le u^* x u` is equivalent to $`x_\lambda \le x`, and so
$`\sup(u^* x_\lambda u) = u^* \sup(x_\lambda) u = u^* x u` if $`u \in M` is invertible.

If $`a \in M` is not invertible, one can shift the spectrum horizontally to avoid zero, i.e.
there is a $`c > 0` so that $`c1 + a` is invertible. Indeed, observe that
$`a - t1 = (a + c1) - (t + c)1` and therefore
$`t \in \sigma(a) \iff t + c \in \sigma(a + c1)`. In particular, if we let $`t = -c` here we
find that $`0 \in \sigma(a) + c \iff 0 \in \sigma(a + c1)`. By the invertible case above,

$$`\begin{aligned}
c^2 \varphi(x_\lambda) + c \varphi(a^* x_\lambda + x_\lambda a) + \varphi(a^* x_\lambda a)
  &= \varphi((c1 + a)^* x_\lambda (c1 + a)) \\
  &\to \varphi((c1 + a)^* x (c1 + a))
\end{aligned}`

for all $`\varphi \in T`. It suffices to show that
$`\varphi(a^* x_\lambda + x_\lambda a) \to \varphi(a^* x + x a)` for all $`\varphi \in T`,
because then $`\varphi(a^* x_\lambda a) \to \varphi(a^* x a)` by the above. We can use
Cauchy-Schwarz ({bpref "lem:cauchy_schwarz"}[]) for this as follows. If $`\alpha \le \beta`, we have
$`x_\beta - x_\alpha \ge 0`, and since the net $`(x_\lambda)` is uniformly bounded there
exists $`M > 0` such that (using {bpref "lem:selfadjoint_le_norm"}[])

$$`\begin{aligned}
|\varphi(a^* (x_\beta - x_\alpha))|
  &= |\varphi(a^* (x_\beta - x_\alpha)^{1/2} (x_\beta - x_\alpha)^{1/2})| \\
  &\le \varphi(a^* (x_\beta - x_\alpha) a)^{1/2} \varphi(x_\beta - x_\alpha)^{1/2} \\
  &\le 2M \varphi(a^* a)^{1/2} \varphi(x_\beta - x_\alpha)^{1/2}
\end{aligned}`

and by the positivity of $`\varphi` we have
$`|\varphi(a^* (x_\beta - x_\alpha))| = |\varphi((x_\beta - x_\alpha) a)|`. It follows that
$`\varphi(a^* x_\lambda + x_\lambda a) \to \varphi(a^* x + x a)`, and the proof is finished.
:::

# Normal Implies Ultraweakly Continuous

If $`P : \mathcal{P}(M) \to \mathrm{Prop}` is a predicate, the usual ordering $`\le` on
projections induces an order on the set $`\{p \in \mathcal{P}(M) \mid P(p)\}`. In what
follows there will be no confusion if we also denote this induced order by $`\le`.

:::lemma_ "lem:exists_uw_ge_normal" (lean := "Ultraweak.exists_lt_of_ne_zero") (uses := "lem:uw_pos_sep_pts")
For every positive normal linear functional $`\varphi` and nonzero $`p \in \mathcal{P}(M)`
there exists a positive $`\sigma(M, M_*)`-continuous linear functional $`\psi` such that
$`\varphi(p) < \psi(p)`.
:::

:::proof "lem:exists_uw_ge_normal"
By {bpref "lem:uw_pos_sep_pts"}[] there is a $`\sigma(M, M_*)`-continuous positive linear
functional $`\psi_0` on $`M` such that $`\psi_0(p) \ne 0`. Rescale this functional by a
positive constant to obtain $`\psi` such that $`\varphi(p) < \psi(p)`.
:::

:::lemma_ "lem:msr_th_lemma" (lean := "Ultraweak.exists_forall_lt") (uses := "lem:sigma_cont_of_normal_Sak_1_7_4, lem:directed_sup_proj, cor:proj_sub_of_subproj")
For all positive linear functionals $`\varphi, \psi` with $`\varphi` normal and $`\psi`
$`\sigma(M, M_*)`-continuous and every nonzero $`p \in \mathcal{P}(M)` such that
$`\varphi(p) < \psi(p)`, there exists a nonzero $`p_1 \in \mathcal{P}(M)` such that
$`p_1 \le p` and for all nonzero $`q \in \mathcal{P}(M)` with $`q \le p_1`, we have
$`\varphi(q) < \psi(q)`.
:::

:::proof "lem:msr_th_lemma"
We proceed by contradiction. Suppose the conclusion does not hold. Then, for every nonzero
subprojection $`p_1` of $`p` there is a nonzero subprojection $`q \le p_1` such that
$`\varphi(q) \ge \psi(q)`. In particular, (letting $`p_1 = q`) there is a $`q \le p` such
that $`\varphi(q) \ge \psi(q)`. If $`(q_\alpha)` is a chain of such nonzero projections, then
$`q_\alpha \to \sup q_\alpha` in the $`\sigma`-topology by
{bpref "lem:sigma_cont_of_normal_Sak_1_7_4"}[], and by
{bpref "lem:directed_sup_proj"}[] we know this supremum is a subprojection of
$`p_1`. Since $`\varphi` is positive and normal, and $`\psi` is positive and
$`\sigma`-continuous, we have
$`\varphi(\sup q_\alpha) \ge \psi(\sup q_\alpha)`.

Therefore, by Zorn's Lemma, there is a maximal $`q_0 \le p` such that
$`\varphi(q_0) \ge \psi(q_0)`. We claim $`q_0 = p`. If not, $`p - q_0` is a nonzero
subprojection of $`p` by {bpref "cor:proj_sub_of_subproj"}[], and there exists a nonzero
projection $`q_1 \le p - q_0` such that $`\varphi(q_1) \ge \psi(q_1)`. But then $`q_0` is a
proper subprojection of $`q_0 + q_1` and by linearity and positivity
$`\varphi(q_0 + q_1) \ge \psi(q_0 + q_1)`, contradicting the maximality of $`q_0`. Thus
$`p = q_0` and so $`\varphi(p) \ge \psi(p)`, contradicting the hypothesis
$`\varphi(p) < \psi(p)`.
:::

The following likely contains the most crucial use of the normality of $`\varphi` for the
later proof of {bpref "thm:sigma_cts_of_normal_Sak_1_13_2"}[].

:::lemma_ "lem:zorn_base" (lean := "Ultraweak.exists_maximal_continuous_mul_right") (uses := "cor:proj_sub_of_subproj, lem:selfadjoint_le_norm, lem:sigma_cont_of_normal_Sak_1_7_4, lem:directed_sup_proj, lem:cauchy_schwarz, prop:loc_cvx_result, def:sigma_top")
Let $`\varphi` be a normal positive linear functional on $`M` and consider the predicate
$`P : \mathcal{P}(M) \to \mathrm{Prop}` defined, for $`p \in \mathcal{P}(M)`, by
"$`M \ni x \mapsto \varphi(xp)` is $`\sigma(M, M_*)`-continuous". If $`(p_\alpha)` is a chain
of projections in $`M` such that $`P(p_\alpha)` is true for each $`\alpha`, then
$`P(\sup(p_\alpha))` is true. Hence by Zorn's Lemma there is a maximal
$`p_0 \in \mathcal{P}(M)` such that $`P(p_0)` is true.
:::

:::proof "lem:zorn_base"
Let $`x` be on the unit sphere and let $`p` be the supremum of the $`p_\alpha`. By
{bpref "lem:sigma_cont_of_normal_Sak_1_7_4"}[] and
{bpref "lem:directed_sup_proj"}[] we know $`p_\alpha` converges in the
$`\sigma`-topology to $`p`, and $`p` is a projection. By
{bpref "cor:proj_sub_of_subproj"}[] we know $`p - p_\alpha` is a projection. By the
$`C^*`-property of the norm ($`\|x^* x\| = \|x\|^2`),
{bpref "lem:selfadjoint_le_norm"}[] and the positivity of $`\varphi` we have
$`\varphi(x^* x) \le \varphi(1)`. Now these facts together with Cauchy-Schwarz and the
monotonicity of square roots ({bpref "lem:cauchy_schwarz"}[]) give

$$`\begin{aligned}
|\varphi(x(p - p_\alpha))|
  &\le \varphi(x^* x)^{1/2} \varphi(p - p_\alpha)^{1/2} \\
  &\le \varphi(1)^{1/2} \varphi(p - p_\alpha)^{1/2}.
\end{aligned}`

Hence, by the definition of the operator norm,
$`\|\varphi(\cdot (p - p_\alpha))\| \le \varphi(1)^{1/2} \varphi(p - p_\alpha)^{1/2}`. The
right hand side converges to $`0` with $`\alpha` due to the normality of $`\varphi`, and
therefore $`\varphi(\cdot\, p_\alpha)` converges to $`\varphi(\cdot\, p)` in norm. Since the
set of $`\sigma`-continuous functionals on $`M` is norm closed, it follows that
$`\varphi(\cdot\, p)` is $`\sigma`-continuous. We obtain a maximal $`p_0` by Zorn's Lemma.
:::

:::lemma_ "lem:dominated_sigma_cts" (lean := "Ultraweak.continuous_of_norm_sq_le") (uses := "lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8, prop:loc_cvx_result")
Let $`\psi` be a $`\sigma`-continuous positive linear functional on $`M`, and let $`\omega` be a
bounded linear functional on $`M` such that $`|\omega(x)|^2 \le C \psi(x^* x)` for all
$`x \in M`. Then $`\omega` is $`\sigma`-continuous.
:::

:::proof "lem:dominated_sigma_cts"
The functional $`\omega` factors through a bounded functional on the GNS Hilbert space
$`H_\psi` of $`\psi`, which by the Riesz representation theorem is $`\langle \eta, \cdot \rangle`
for some $`\eta \in H_\psi`. Approximating $`\eta` by the classes $`\hat y` of elements
$`y \in M`, the functionals $`x \mapsto \psi(y^* x)` converge in norm to $`\omega`. These are
$`\sigma`-continuous by {bpref "lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8"}[], and the
$`\sigma`-continuous functionals form a norm closed subspace of $`M^*`
({bpref "prop:loc_cvx_result"}[]).
:::

This replaces the use of the strong ($`s`-) topology in Sakai's proof of
{bpref "thm:sigma_cts_of_normal_Sak_1_13_2"}[]: Sakai shows that $`\sigma(M, M_*)` and the
$`s`-topology agree on bounded sets ({bpref "thm:sigma_le_s_le_tau"}[],
{bpref "cor:sigma_eq_s_on_ball"}[], which need the Mackey topology and the Mackey–Arens theorem),
so that a functional is $`\sigma`-continuous if and only if it is $`s`-continuous on the unit ball
({bpref "lem:bdd_sigma_cts_iff_bdd_s_cts_Sak_1_8_10"}[]). The GNS argument above avoids all of
this.

:::lemma_ "lem:corner_comparison" (lean := "Ultraweak.map_le_map_of_forall_lt, PositiveLinearMap.le_of_le_on_isStarProjection") (uses := "lem:cut_down_of_wstar, lem:wstar_pos_approx_proj")
Let $`\varphi, \psi` be positive linear functionals on $`M` and $`p` a projection such that
$`\varphi(q) < \psi(q)` for every nonzero projection $`q \le p`. Then
$`\varphi(a) \le \psi(a)` for every positive $`a \in pMp`.
:::

:::proof "lem:corner_comparison"
By {bpref "lem:cut_down_of_wstar"}[], $`pMp` is a $`W^*`-algebra whose projections are exactly the
projections $`q \le p` of $`M`. By {bpref "lem:wstar_pos_approx_proj"}[] applied in $`pMp`, every
positive $`a \in pMp` is a norm limit of nonnegative combinations of such projections, and the set
where $`\varphi \le \psi` is a norm closed convex cone.
:::

:::theorem "thm:sigma_cts_of_normal_Sak_1_13_2" (lean := "Ultraweak.continuous_of_scottContinuousOn, Ultraweak.continuous_of_scottContinuousOn_chains") (uses := "def:sigma_top, lem:zorn_base, lem:exists_uw_ge_normal, lem:msr_th_lemma, lem:corner_comparison, lem:dominated_sigma_cts, lem:cauchy_schwarz, lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8")
(Sakai 1.13.2) Every positive normal linear functional $`\varphi` on $`M` is
$`\sigma(M, M_*)`-continuous.
:::

:::proof "thm:sigma_cts_of_normal_Sak_1_13_2"
The claim is obvious for the zero functional. Let $`\varphi` be a nonzero positive normal
linear functional. By {bpref "lem:zorn_base"}[] we have a maximal $`p_0 \in \mathcal{P}(M)`
such that $`M \ni x \mapsto \varphi(x p_0)` is $`\sigma(M, M_*)`-continuous. Assume for the
purposes of finding a contradiction that $`p_0 \ne 1`. By
{bpref "lem:exists_uw_ge_normal"}[] there is a $`\sigma(M, M_*)`-continuous positive
functional $`\psi` on $`M` such that $`\varphi(1 - p_0) < \psi(1 - p_0)`. By
{bpref "lem:msr_th_lemma"}[] there is a nonzero subprojection $`p \le 1 - p_0` in $`M` such
that $`\varphi(q) < \psi(q)` for every nonzero $`q \le p` in $`M`.

By {bpref "lem:corner_comparison"}[], $`\varphi(p x^* x p) \le \psi(p x^* x p)` for every
$`x \in M`. The functional $`\psi' = \psi(p \cdot p)` is positive and $`\sigma`-continuous by
{bpref "lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8"}[], and by the Cauchy–Schwarz inequality
({bpref "lem:cauchy_schwarz"}[])

$$`|\varphi(xp)|^2 \le \varphi(1) \varphi(p x^* x p) \le \varphi(1) \psi'(x^* x).`

Hence $`x \mapsto \varphi(xp)` is $`\sigma`-continuous by {bpref "lem:dominated_sigma_cts"}[], and
therefore so is $`x \mapsto \varphi(x(p_0 + p)) = \varphi(x p_0) + \varphi(xp)`. Since $`p_0 + p` is a
projection strictly larger than $`p_0`, this contradicts the maximality
of $`p_0`, and therefore $`p_0 = 1` and the result follows.
:::

The above result gives us that the $`\sigma`-weak continuity of a positive functional is
determined entirely by the order structure on $`M`, and thus is independent of the choice of
predual.

# Sakai's Theorem and the Uniqueness of the Predual

:::theorem "thm:sakai_normal_iff" (lean := "Ultraweak.positive_tfae, Ultraweak.scottContinuous_of_scottContinuousOn_chains") (uses := "lem:sigma_cont_of_normal_Sak_1_7_4, thm:sigma_cts_of_normal_Sak_1_13_2, prop:loc_cvx_result")
For a positive linear functional $`\varphi` on a $`W^*`-algebra $`M` with predual $`M_*`, the
following are equivalent:

1. $`\varphi` is $`\sigma(M, M_*)`-continuous;
2. $`\varphi` lies in (the image of) $`M_*`;
3. $`\varphi` preserves suprema of bounded directed sets;
4. $`\varphi` preserves suprema of directed sets of projections.
:::

:::proof "thm:sakai_normal_iff"
(1) and (2) are equivalent by {bpref "prop:loc_cvx_result"}[]. (1) implies (3) by
{bpref "lem:sigma_cont_of_normal_Sak_1_7_4"}[], (3) trivially implies (4), and (4) implies (1) by
{bpref "thm:sigma_cts_of_normal_Sak_1_13_2"}[].
:::

:::theorem "thm:predual_unique" (lean := "Ultraweak.continuousLinearEquivOfPredual, Predual.uniqueEquiv") (uses := "thm:sakai_normal_iff, lem:sigma_eq_weak_pos_on_bdd, thm:krein_smulian, prop:loc_cvx_result")
If $`P` and $`Q` are preduals of a $`W^*`-algebra $`M`, then $`\sigma(M, P) = \sigma(M, Q)`, and
there is a canonical isometric isomorphism $`P \cong Q` compatible with the pairings with $`M`.
:::

:::proof "thm:predual_unique"
By {bpref "thm:sakai_normal_iff"}[], the positive $`\sigma(M, P)`-continuous functionals are the
positive $`\sigma(M, Q)`-continuous functionals, since condition (4) does not mention the predual.
On bounded sets, each ultraweak topology is the weak topology induced by its positive continuous
functionals ({bpref "lem:sigma_eq_weak_pos_on_bdd"}[]), so the two topologies agree on the
unit ball. By the Krein–Smulian theorem ({bpref "thm:krein_smulian"}[]), the identity of $`M` is a
homeomorphism $`\sigma(M, P) \to \sigma(M, Q)`. Hence $`P` and $`Q` are identified, via their
isometric embeddings into $`M^*`, with the same subspace of $`M^*`
({bpref "prop:loc_cvx_result"}[]).
:::
