import LeanOABlueprint.Base

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dual Pairs and Weak Topologies" =>

This chapter collects the locally convex input to the rest of the blueprint. Throughout,
$`\mathbb{K}` is $`\mathbb{R}` or $`\mathbb{C}`, and $`B : E \times F \to \mathbb{K}` is a bilinear
form, or *pairing*, between vector spaces $`E` and $`F`. The ultraweak topology on a
$`W^*`-algebra $`M` is the case $`E = M`, $`F = M_*`. Most of the results here are destined for
mathlib.

:::definition "def:weak_top" (lean := "WeakBilin, LinearMap.IsWeak")
The *weak topology* $`\sigma(E, F)` on $`E` is the coarsest topology for which the functionals
$`x \mapsto B(x, y)` are continuous for every $`y \in F`. We say that a topology on $`E` *is weak*
for $`B` if it coincides with $`\sigma(E, F)`.
:::

:::definition "def:compatible_dual" (lean := "LinearMap.IsCompatibleDual")
A topology on $`E` is *compatible* with $`B` if every continuous linear functional on $`E` is of
the form $`x \mapsto B(x, y)` for exactly one $`y \in F`; that is, $`y \mapsto B(\cdot, y)` is a
linear isomorphism of $`F` onto the continuous dual $`E'` of $`E`.
:::

:::lemma_ "lem:weak_dual" (lean := "LinearMap.IsWeak.eval_surjective, LinearMap.IsWeak.rightDualEquiv") (uses := "def:weak_top, def:compatible_dual")
Every $`\sigma(E, F)`-continuous linear functional on $`E` is of the form $`B(\cdot, y)` for some
$`y \in F`. Consequently, if $`B` separates the points of $`F`, then $`\sigma(E, F)` is compatible
with $`B`.
:::

:::proof "lem:weak_dual"
If $`f` is $`\sigma(E, F)`-continuous, then $`|f(x)| \le C \max_i |B(x, y_i)|` for some
$`C \ge 0` and finitely many $`y_1, \ldots, y_n \in F`. So $`f` vanishes on the common kernel of
the functionals $`B(\cdot, y_i)`, and is therefore a linear combination of them, which is
$`B(\cdot, y)` for some $`y` in the span of the $`y_i`. Uniqueness of $`y` is exactly the
statement that $`B` separates the points of $`F`.
:::

:::theorem "thm:Banach_Alaoglu" (tags := "mathlib") (lean := "WeakDual.isCompact_closedBall")
(Banach-Alaoglu) The closed unit ball of the dual space of a normed vector space is compact
in the weak-$`*` topology.
:::

For $`s \subseteq E`, the *polar* of $`s` is
$`s^\circ = \{y \in F \mid |B(x, y)| \le 1 \text{ for all } x \in s\}`, and the polar of a subset
of $`F` is defined symmetrically.

:::theorem "thm:bipolar" (lean := "LinearMap.flip_polar_polar, LinearMap.IsCompatibleDual.flip_polar_polar") (uses := "def:weak_top, def:compatible_dual, lem:weak_dual")
(Bipolar theorem) Suppose that $`E` carries the weak topology $`\sigma(E, F)`, or more generally
a locally convex topology compatible with $`B`. Then for every nonempty $`s \subseteq E`, the
bipolar $`s^{\circ\circ}` is the closed absolutely convex hull of $`s`.
:::

:::proof "thm:bipolar"
The bipolar is closed, absolutely convex, and contains $`s`, so it contains the closed absolutely
convex hull $`K` of $`s`. Conversely, if $`x_0 \notin K`, the Hahn–Banach separation theorem
yields a continuous linear functional $`f` on $`E` and a real number $`c > 0` with
$`|f(x)| \le c < \operatorname{Re} f(x_0)` for all $`x \in K`. By {bpref "lem:weak_dual"}[], or
by compatibility, $`f = B(\cdot, y)` for some $`y \in F`, so $`y / c \in s^\circ` while
$`|B(x_0, y / c)| > 1`, and therefore $`x_0 \notin s^{\circ\circ}`.
:::

:::corollary "cor:bipolar_submodule" (lean := "LinearMap.IsWeak.flip_polarSubmodule_polarSubmodule, LinearMap.IsCompatibleDual.flip_polarSubmodule_polarSubmodule") (uses := "thm:bipolar")
Under the hypotheses of {bpref "thm:bipolar"}[], let $`W \subseteq E` be a subspace. Then
$`W^\circ` is the annihilator $`W^\perp = \{y \in F \mid B(x, y) = 0 \text{ for all } x \in W\}`,
and $`(W^\perp)^\perp` is the closure of $`W`.
:::

:::proof "cor:bipolar_submodule"
Since $`W` is closed under scaling, $`|B(x, y)| \le 1` for all $`x \in W` forces $`B(x, y) = 0`,
so $`W^\circ = W^\perp`, and likewise for subspaces of $`F`. The closed absolutely convex hull of
a subspace is its closure, so the claim follows from {bpref "thm:bipolar"}[].
:::

:::theorem "thm:krein_smulian" (lean := "krein_smulian, krein_smulian_of_submodule, LinearMap.IsWeak.continuous_of_continuousOn_closedBall") (uses := "thm:Banach_Alaoglu, def:weak_top, def:compatible_dual")
(Krein–Smulian) Let $`E` be a Banach space. A convex subset of $`E^*` is weak-$`*` closed if its
intersection with every closed ball is weak-$`*` closed. Consequently, if $`B : X \times E \to
\mathbb{K}` identifies $`X` with $`E^*` (that is, $`\sigma(E, X)` is compatible with $`B`) and
$`X` carries the weak topology $`\sigma(X, E)`, then a convex cone in $`X` is closed as soon as its
intersection with the closed unit ball is closed, and a linear map from $`X` into a space carrying
a weak topology is continuous as soon as it is continuous on the closed unit ball.
:::

:::proof "thm:krein_smulian"
The first statement is proved by an inductive construction of a sequence of finite sets in
$`E`, tending to zero, whose polars separate a point outside the convex set from the set itself;
compactness of the intersections with closed balls ({bpref "thm:Banach_Alaoglu"}[]) drives each
step. For the consequences, $`X` is homeomorphic to $`E^*` with its weak-$`*` topology, and a
linear map into a weak topology is continuous if and only if each of its compositions with the
defining functionals is; the preimage of a closed set under such a composition, intersected with
a closed ball, is closed by hypothesis.
:::
