/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoSlides
import Verso.Doc.Concrete
import Illuminate
import LeanOA.Mackey
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import LeanOA.Ultraweak.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import LeanOA.KreinSmulian
import LeanOA.Ultraweak.Masa
import LeanOA.Ultraweak.LUB

open VersoSlides

set_option linter.unusedVariables false
set_option verso.code.warnLineLength 65
set_option autoImplicit true
set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Slides) "Formalizing operator algebras in Lean" =>

# What is Lean? Formalization?

+ [Lean](https://lean-lang.org): programming language and interactive theorem prover.
+ [Mathlib](https://mathlib.org): Lean's community-driven monolithic library of mathematics.
+ *Formalization*: encoding mathematical definitions, statements, and proofs in a
  formal language that can be checked by a computer.
+ *Operator algebras*: a branch of functional analysis which, from a category-theoretic perspective,
  can be interepreted as the study of noncommutative function spaces (a.k.a. noncommutative
  topology, or noncommutative measure theory, or even noncommutative geometry).
+ [LeanOA](https://j-loreaux.github.io/LeanOA/) a GitHub repo for Lean formalization specific to
  operator algebras, with a focus to upstream material to Mathlib.

:::notes
Interactive theorem provers (also known as *proof assistants*) have existed for decades, examples
include Isabelle, HOL light, Mizar, Rocq, Automath, Agda, etc.

Lean is a relatively new proof assistant, but it has quickly gained popularity, especially in the
mathematics community.
:::

# No, but really, what is Lean?

```lean
def IsPrime (n : Nat) :=
  1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

-- !fragment
theorem exists_prime_factor :
    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by
  intro n h1
  -- Either `n` is prime...
  by_cases hprime : IsPrime n
  · grind [Nat.dvd_refl]
-- !fragment
  -- ... or some divisor has a prime factor
  · obtain ⟨k, _⟩ :
        ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all [IsPrime]
    obtain ⟨p, _, _⟩ :=
      exists_prime_factor k (by grind)
    grind [Nat.dvd_trans]
```

# Why formalize mathematics?

Patrick Massot wrote [an excellent short essay](https://www.imo.universite-paris-saclay.fr/~patrick.massot/files/exposition/why_formalize.pdf)
on this.

1. Correctness ─ across all scales
2. Explanation ─ dynamic level of detail
3. Pedagogy ─ visualized proof state
4. Research ─ reformulating in real time
5. Collaboration ─ many collaboratrs, different backgrounds
6. Built to last ─ work now can have enduring impact

:::notes
+ small, medium and large scale correctness
+ dynamic level of detail in a proof
+ tactic state and context
+ checking, outlining, reformulating, linting unused assumptions
+ enjoying collaborating with a wide variety of mathematicians
:::

# Operator algebras (concretely)

```lean -show
section
set_option linter.unusedVariables false
variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {a : V →L[𝕜] V}
```

+ {lean}`V`: _Banach space_ over a field $`𝕜`
+ {lean}`V →L[𝕜] V`: continuous $`𝕜`-linear maps from $`V` to itself
+ such maps form a _normed algebra_ under composition and the operator norm $`(0, 1, +, ∘, •, ‖⬝‖)`
+ if {lean}`V` is also a _Hilbert space_, then {lean}`V →L[𝕜] V`
  has a conjugate-linear antimultiplicative involution {lean}`(star : (V →L[𝕜] V) → (V →L[𝕜] V))`
  called the _adjoint_.
+ satisfies {lean}`‖star a * a‖ = ‖a‖ ^ 2` for all {lean}`(a : V →L[𝕜] V)`.
+ a _(concrete) C\*-algebra_ is a norm-closed \*-subalgebra of {lean}`V →L[𝕜] V`.
+ a _(concrete) von Neumann algebra_ is a C\*-algebra that is also closed in the _weak operator
  topology_.

:::notes
+ Banach space = _complete normed vector space_
+ $`𝕜` is $`ℝ` or $`ℂ`, generally $`ℂ`
+ Hilbert space = _complete inner product space_
If you've studied finite dimensional linear algebra, you will have studied the analogous structure
of linear maps. Continuous ones are the natural generalization to infinite dimensions.
+ Note that this involves many supplementary structures
+ other definitions of _von Neumann algebra_ could be given, e.g. closed in the strong operator
  topology, or equal to its own double commutant, etc.
:::

```lean -show
end
```

# Operator algebras (abstractly)

```lean -show
section
set_option linter.unusedVariables false
variable {X A : Type*} [CStarAlgebra A] {a : A} [TopologicalSpace X]
```

+ An _(abstract) C\*-algebra_ is a Banach algebra {lean}`A` over {lean}`ℂ` with a conjugate-linear
  antimultiplicative involution {lean}`(star : A → A)` such that {lean}`‖star a * a‖ = ‖a‖ ^ 2`
  for all {lean}`(a : A)`.
+ Easier to work with, and {lean}`C(X, ℂ)` can be a C\*-algebra when {lean}`X` is a compact
  Hausdorff space.
+ Every abstract C⋆-algebra is isomorphic to a concrete one, so no loss of generality.
+ What about von Neumann algebras? Not so easy, as the concrete definition seems to depend on
  the structure as a subalgebra of continuous linear maps.

:::notes
+ Note the simplicity of this definition for abstract C\*-algebras.
+ At the same time, certain algebras should certainly be von Neumann algebras, e.g.,
  bounded measurable functions on a measure space, but how to capture this abstractly?
:::

```lean -show
end
```

# Operator topology zoo

:::hstack
+ norm: {lean}`@ContinuousLinearMap`
+ strong operator: {lean}`@PointwiseConvergenceCLM`
+ weak operator: {lean}`@ContinuousLinearMapWOT`
+ weak Banach: {lean}`@WeakSpace`
+ others not previously formalized
+ most involve topologies defined via a _predual_

{image "Optop.svg" (height := "100%")}[Operator topologies]
:::

# Preduals, W\*-algebras and von Neumann algebras

```lean -show
section
set_option linter.unusedVariables false
variable {𝕜 X P : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup P] [NormedSpace 𝕜 P] [NormedSpace ℂ P] [CompleteSpace P]
variable {M : Type*} [CStarAlgebra M] [Predual ℂ M P]
```

+ A _predual_ of a Banach space {lean}`X` is a Banach space {lean}`P` such that
  {lean}`X ≃ₗᵢ[𝕜] (P →L[𝕜] 𝕜)`.
+ A _W\*-algebra_ is a C\*-algebra that admits a predual.
+ _Sakai's theorem_: every W\*-algebra can be realized as a von Neumann algebra,
  and every W\*-algebra has a _unique_ predual.

Thus W\*-algebras constitute the abstract characterization of von Neumann algebras.

:::fragment fadeUp
Project goals:
+ Develop API for preduals and W\*-algebras, allowing for distinct preduals even though they
  are unique up to isomorphism.
+ Construct the various operator topologies (ultraweak, ultrastrong, ultrastrong-\*,
  Arens–Mackey) on W\*-algebras, and establish their inclusions
+ Show that the ultraweak topology on a W\*-algebra makes it into a semitopological star algebra.
+ Prove Sakai's theorem
:::

```lean -show
end
```

# The importance of the abstract approach
%%%
vertical := true
%%%

```lean -show
section
set_option linter.unusedVariables false
variable {n : ℕ}
```

+ analogy with finite-dimensional real vector spaces and {lean}`Fin n → ℝ`;
  without abstraction, wouldn't work for {lean}`ℝ × ℝ`, or {lean}`ℂ`, or even
  {lean}`EuclideanSpace ℝ (Fin n)`.
+ sometimes mathematicians lie; example: the first isomorphism theorem
+ {lean}`Type` versus {lean}`Prop`. Data, diamonds and forgetful inheritance.

```lean -show
end
```

## Sometimes mathematicians lie

_Theorem (First isomorphism theorem)._ Let $`G` and $`H` be groups and let $`f : G → H` be a
surjective group homomorphism. Then $`G / \ker f ≃ H`.

:::fragment fadeUp
Does anyone see the problem with this statement?
:::

:::fragment fadeUp
Note: it's _not_ false.
:::

:::fragment fadeUp
The lie is one of omission: the isomorphism is the one induced by $`f` and the universal property
of the quotient. Moral of the story: _data matters_.
:::

:::notes
Yes, I'm being intentionally provacative here.
:::

## Data, diamonds and forgetful inheritance

Consider the following two facts:

1. Every metric space induces a corresponding topology, with a basis of the topology given by
  open balls.
2. Given any two topological spaces, the product can be made into a topological space using the
  product topology.

::::fragment fadeUp
What should be the topology on {lean}`ℝ × ℝ`? You want it to be:

+ automatically inferred by Lean so you don't _always_ have to specify it
+ agree with the topology induced by the metric† on {lean}`ℝ × ℝ`
+ agree with the product topology on {lean}`ℝ × ℝ` induced by the topology on {lean}`ℝ`
:::fragment fadeUp
+ key insight: these are fundamentally at odds unless you bake the topology, and its compatibility
  with the metric, into the definition of a {lean}`MetricSpace`.
:::

:::notes
Actually, the metric we put on {lean}`ℝ × ℝ` is not the Euclidean metric, but the sup metric,
but the point still stands.
:::

::::

## Preferring {lean}`WStarAlgebra` over {lean}`VonNeumannAlgebra`?

+ The former is a {lean}`Prop`osition, it carrries no data, so no risk of diamonds.
+ The former applies to any abstract C\*-algebra, there is no need to carry around a Hilbert space
  representation; thus even {lean}`ContinuousMap` can be a W\*-algebra with the right hypotheses
  on the domain.
+ Downside: because of the lack of data, we don't get to choose our predual on demand.
  Hence the importance of Sakai's theorem.

:::notes
{lean}`ContinuousMap` is the type of _all_ continuous maps between two topological spaces.
:::

# The road to Sakai's theorem

> The rabbit-hole went straight on like a tunnel for some way, and then dipped suddenly down,
  so suddenly that Alice had not a moment to think about stopping herself before she found herself
  falling down a very deep well.

:::fragment fadeUp
{image "sakai-theorem.png" (width := "70%")}[Sakai's theorem]
:::

:::fragment fadeUp
> You take the blue pill, the story ends. You wake up in your bed and believe whatever you want to.
  You take the red pill, you stay in Wonderland, and I show you how deep the rabbit hole goes.
:::

# The ultraweak topology
%%%
vertical := true
%%%

{image "sakai-ultraweak-def.png" (width := "70%")}[ultraweak topology on a W\*-algebra]

:::fragment fadeUp
```lean
#print Ultraweak
```
:::

:::notes
+ We need a type synonym, `M` _already has a topology_ induced by the norm since it is a
  C\*-algebra.
+ The ultraweak topology _a priori_ depends on the choice of predual, but Sakai's theorem
  _a fortiori_ implies that all choices give the same topology.
:::

## The first lemma

{image "sakai-1-7-1-part-1.png" (width := "80%")}[Sakai 1.7.1]

$`S` is the closed unit ball, $`P` is the collection of nonnegative elements, $`M^s` is the
collection of self-adjoint elements.

## The first lemma (continued)

{image "sakai-1-7-1-part-2.png" (width := "80%")}[Sakai 1.7.1]

We already had all the tools to make this work *except* the _Krein–Smulian theorem_.

## The Krein–Smulian theorem

```lean
#check krein_smulian
#check krein_smulian_of_submodule
```

:::fragment fadeUp
We had some of the tools to prove this, _except_ (the Banach space of) sequences converging to
zero and that for the scalar-valued case, it's dual consists of summable sequences.
:::

## The strong dual of sequences convergence to zero

```lean
#print tendstoZero
#check tendstoZero.lpOneToStrongDualₗᵢ
```

:::fragment fadeUp
We had the tools to prove this, _except_ we didn't have a version of Hölder's inequality that was
suitable.

```lean
#check Real.inner_le_Lp_mul_Lq_of_nonneg
```
:::

# Of conditionally complete partial orders

{image "sakai-1-7-4.png" (width := "70%")}[Sakai 1.7.4]

+ created {lean}`ConditionallyCompletePartialOrderSup`
+ aside: an order structure on {lean}`ℂ`
+ need uniform space structures on spaces with a weak topology

:::notes
the formalization of this lemma uncovered a (minor) error in the original proof.
:::

# Wait, it gets even deeper?!
%%%
vertical := true
%%%

```lean -show
open scoped ComplexOrder
open LinearMap.IsWeak
variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [τ : TopologicalSpace E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
```

{image "need-for-mackey-arens.png" (width := "70%")}[Sakai 1.7.4]

ultraweak ≤ ultrastrong ≤ ultrastrong-∗ ≤ Arens–Mackey

:::fragment fadeUp
_Mackey–Arens Theorem._ A locally convex topology {lean}`τ` on a vector space {lean}`E` is
compatible with a dual pairing {lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` (i.e., {lean}`F ≃ₗ[𝕜] StrongDual 𝕜 E`)
if and only if {lean}`τ` is the topology of uniform convergence on a family of absolutely convex,
weakly compact sets in {lean}`F`.
:::

## So much to unpack here!

_Mackey–Arens Theorem._ A locally convex topology {lean}`τ` on a vector space {lean}`E` is
compatible with a dual pairing {lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` (i.e., {lean}`F ≃ₗ[𝕜] StrongDual 𝕜 E`)
if and only if {lean}`τ` is the topology of uniform convergence on a family of absolutely convex,
weakly compact sets in {lean}`F`.

+ {lean}`F`, although _a priori_ is not equipped with a topology, actually needs to be equipped with
  the weak topology relative to {lean}`B` in order for the statement to make sense (compactness).
  So, maybe {lean}`F` should be replaced by {lean}`WeakBilin B.flip`.
+ {lean}`B.IsCompatible` is a concept we had to define in Lean, as it didn't exist previously.
+ The _topology of uniform convergence_ here actually means the _pullback_ (through {lean}`B`) of
  said topology.
+ The _Mackey topology_ (sometimes called the _Arens–Mackey topology_) is the this topology of
  uniform convergence on _all_ absolutely convex, weakly compact sets in {lean}`F`.
+ Thus, the Mackey–Arens theorem is saying that the Mackey topology is the finest locally convex
  topology on {lean}`E` that is compatible with the dual pairing {lean}`B`.

## Weak topologies are not weak topologies?

Also known as: _transparency levels of definitional equalities_. This gets technical.

Consider the natural bilinear map {lean}`topDualPairing 𝕜 E`. We can equip the domain with the
topology of pointwise convergence (a.k.a. the weak-⋆ topology) using
{lean}`WeakBilin (topDualPairing 𝕜 E)`. This is exactly {lean}`WeakDual 𝕜 E`, but only at default
transparency:
```lean
#print WeakDual
```
```lean +error
example : (inferInstance : TopologicalSpace (WeakDual 𝕜 E)) =
  (inferInstance : TopologicalSpace (WeakBilin (topDualPairing 𝕜 E)))
    := by
  with_reducible_and_intances rfl
```

## A type class for weak topologies

To circumvent the problems in the previous slide, we introduced a type class which encodes the fact
that a topological space is equipped with the weak topology relative to a given bilinear map.
This is {lean}`B.IsWeak`

We can now show that several extant topologies satisfy this property:
{lean}`@instFlip`, {lean}`@instWeakBilinPairing`, {lean}`@instWeakBilinFlipPairing`,
{lean}`@instWeakSpaceStrongDualWeakSpacePairing`, {lean}`@instWeakDualWeakDualPairing`

```lean
-- A generic bipolar theorem for weak topologies
example (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) [hB : B.IsWeak]
    {s : Set E} (hs : s.Nonempty) :
    B.flip.polar (B.polar s) = (closedAbsConvexHull 𝕜) s :=
  B.bipolar hs

-- works for any bilinear form satisfying `IsWeak`.
example {s : Set (WeakDual 𝕜 E)} (hs : s.Nonempty) :
    (weakDualPairing 𝕜 E).flip.polar ((weakDualPairing 𝕜 E).polar s) =
      (closedAbsConvexHull 𝕜) s :=
  (weakDualPairing 𝕜 E).bipolar hs
```

## Polar topologies

A {lean}`@PolarTopology` is a type synonym for {lean}`E` equipped with the topology of uniform
convergence on a collection of von Neumann bounded (relative to the weak topology on {lean}`F`)
sets in {lean}`F` induced by a bilinear map {lean}`B`.

The key tool to prove the Mackey–Arens theorem is that a locally convex topology compatible with a
given bilinear form is, in fact, a polar topology: {lean}`@PolarTopology.polarTopologyNhdsPolars`.
Here the sets for uniform convergence are polars of neighborhoods of zero in the original topology
on {lean}`E`.

## The Mackey topology and the Mackey–Arens theorem

The _Mackey topology_ (sometimes called the _Arens–Mackey topology_) is simply a polar topology
where the collection of von Neumann bounded sets is the collection of _all_ absolutely convex,
weakly compact sets in {lean}`F`.

Because of our {lean}`@LinearMap.IsWeak` type class, we can parameterize this over any bilinear map
satisfying that condition

```lean
#print Mackey
```

Meanwhile, we can also get the (nontrivial) direction of the Mackey–Arens theorem that a locally
convex topology compatible with a given bilinear map is weaker than the Mackey topology. This is
{lean}`@continuous_ofMackey`.

# What we have achieved so far

+ definitions and API for {lean}`Predual`, {lean}`Ultraweak`, {lean}`@PolarTopology`,
  {lean}`@Mackey`, and the various topologies in between,
  such as the ultrastrong and the ultrastrong-⋆ topologies.
+ definitions and API for {lean}`PositiveContinuousLinearMap` and
  {lean}`ConditionallyCompletePartialOrderSup`
+ characterization of extreme points of the unit ball in a C\*-algebra.
+ the {lean}`@krein_smulian` theorem
+ 90% of the way to showing that {lean}`Ultraweak` is a semitopological star algebra.
+ the Mackey–Arens theorem, e.g., {lean}`@continuous_ofMackey`.
+ 50% of the way to Sakai's theorem. For instance, we already have the easier (but still highly
  nontrivial) direction {lean}`@Ultraweak.instSupConvergenceClassComplex`, which shows that
  ultraweakly continuous functionals are normal.
+ All this constitutes about 10k lines of code, all of which we plan to upsream to Mathlib.

# Aside: why not AI?

+ The _end_ isn't the goal, the _process_ is
+ Developing _resusable_ code is absolutely crucial, and AI is generally bad at this
+ Let us not rely on proprietary software for our work as mathematicians
+ AI companies don't play nice

# Some lessons

+ The theory of W\*-algebras requires *significantly* more abstract functional analysis than the
  theory of C\*-algebras.
+ It always takes longer than you think to do it right,
  even if you already understand this principle.
+ Mathematicians are sloppy.
+ Formalization provides new insights that are otherwise hard to glean.
