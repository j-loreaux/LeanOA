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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import LeanOA.Ultraweak.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import LeanOA.KreinSmulian
import LeanOA.Ultraweak.Masa
import LeanOA.Ultraweak.LUB
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

open VersoSlides

set_option linter.unusedVariables false
set_option verso.code.warnLineLength 80
set_option autoImplicit true
set_option linter.hashCommand false
set_option linter.style.emptyLine false

#doc (Slides) "Formalizing operator algebras in Lean" =>

# Obstacles and opportunities in the formalization of operator algebras

Jireh Loreaux

ICERM, 13 May 2026

# Why bother with Mathlib?

+ Reusability
+ Integration
+ Community

# Purpose of the talk

+ Highlight techniques and design patterns that can be used throughout the library
+ Share problems and some solutions to common issues in library development
+ Update on some progress in the formalization of operator algebras
+ Focus on utility for the end user

:::notes
For those less familiar with operator algebras, I will try to keep the talk accessible.
:::

# Operator algebras (concretely)

```lean -show
section
set_option linter.unusedVariables false
variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {a : V →L[𝕜] V}
```

+ {lean}`V`: _Banach space_ over a field $`𝕜` ({lean}`RCLike`)
+ {lean}`V →L[𝕜] V`: continuous $`𝕜`-linear maps from $`V` to itself
+ such maps form a _normed algebra_ under composition and the operator norm $`(0, 1, +, ∘, •, ‖⬝‖)`
+ if {lean}`V` is also a _Hilbert space_, then {lean}`V →L[𝕜] V`
  has a conjugate-linear antimultiplicative involution {lean}`(star : (V →L[𝕜] V) → (V →L[𝕜] V))`
  called the _adjoint_.
+ satisfies {lean}`‖star a * a‖ = ‖a‖ ^ 2` for all {lean}`(a : V →L[𝕜] V)`.
+ a _(concrete) C\*-algebra_ is a norm-closed \*-subalgebra of {lean}`V →L[𝕜] V`.
+ a _(concrete) {lean}`VonNeumannAlgebra`_ is a unital C\*-subalgebra of {lean}`V →L[𝕜] V` that is
  also closed in the _weak operator topology_, or equivalently, a star subalgebra equal to its
  bicommutant (double centralizer).

:::notes
+ $`𝕜` is $`ℝ` or $`ℂ`, generally $`ℂ`
+ this allows for real *concrete* C\*-algebras and von Neumann algebras
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

# Continuous functional calculus
%%%
vertical := true
%%%

+ _Gelfand duality_: there is a contravariant equivalence of categories between compact Hausdorff
  spaces and commutative unital C\*-algebras.
+ In particular, when $`a` is a normal element of a C\*-algebra, the unital C\*-subalgebra generated
  by $`a` is commutative, so isomorphic to $`C(X, ℂ)` for some space $`X`. In
  fact, $`X` is the spectrum of $`a`. This is {lean}`@continuousFunctionalCalculus`.

:::fragment fadeUp
```lean
#check continuousFunctionalCalculus
```
:::

## Unsuitable for formalization

```lean
#check continuousFunctionalCalculus
```

:::fragment fadeIp
+ highly dependently-typed
+ bundled continuous functions, with domain a subtype of $`ℂ`.
+ range is a subtype of the original C\*-algebra
+ specific to normal operators / $`ℂ`.
+ not useful for composition of functions
:::

## Optimizing for usability

```lean
#check ContinuousFunctionalCalculus
```
see {lean}`ContinuousFunctionalCalculus` and {lean}`@cfc`.

:::hstack
+ unbundled functions
+ unbundled elements of the C\*-algebra
+ {lean}`autoParam` for common hypotheses
+ {lean}`outParam` for the predicate
+ multiple scalar fields
+ {lean}`Prop`-valued, no diamonds
+ works for type synonyms
:::

## Downsides and autoParams

+ obvious downside of unbundling: is that we lose the ability to automatically conclude the
  necessary properties (say, that the function is continuous on the spectrum).
+ Must pass around proofs of {lean}`@ContinuousOn`, {lean}`@IsStarNormal`,
  {lean}`@IsSelfAdjoint`, etc. (or, as Terry mentioned the other day, `MemSobolev`).
+ One potential solution: {lean}`autoParam`, see for instance {lean}`@cfc_comp`

```lean
example {A : Type*} [CStarAlgebra A] {f : ℂ → ℂ} {a : A}
    [IsStarNormal a] (hf : Continuous f) :
    cfc (fun x ↦ f (x ^ 2)) a = cfc f (a ^ 2) := by
  rw [cfc_comp' f _ a]; rw [cfc_pow_id ..]
```

## Another example: the need for `simp` modifications

```lean -show
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

open scoped ComplexStarModule
open Complex
```
A step in the proof that unitary elements span any C\*-algebra:
```lean
example (a : A) (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) =
      cfc (fun x : ℂ ↦ x.re + I * √(1 - x.re ^ 2)) a := by
  rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
  case nonneg =>
    rwa [sub_nonneg,
    ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2),
    sq, ha.norm_mul_self, sq_le_one_iff₀ (by positivity)]
  rw [cfc_add ..]; rw [cfc_const_mul ..]
  rw [← cfc_real_eq_complex (fun x ↦ x) ha]
  rw [cfc_id' ℝ a]
  rw [← cfc_real_eq_complex (fun x ↦ √(1 - x ^ 2)) ha]
  rw [cfcₙ_eq_cfc]; rw [cfc_comp' (√·) (1 - · ^ 2) a]
  rw [cfc_sub ..]; rw [cfc_pow ..]
  rw [cfc_const_one ..]; rw [cfc_id' ..]
```
This yields the following opportunity for a bespoke tactic: `cfc_pull`

## Selected results utilizing the functional calculus

+ A few due to Frédéric Dupuis:
  {lean}`@CFC.monotone_rpow`, {lean}`@CFC.concaveOn_rpow`,
  {lean}`@CStarAlgebra.convexOn_ringInverse`,
  {lean}`@CFC.log_monotoneOn`, {lean}`@CFC.concaveOn_log`
+ Some continuity results:
  {lean}`@continuousOn_cfc_setProd`, {lean}`@Continuous.cfc_of_mem_nhdsSet`,
  {lean}`@CFC.continuous_abs`

```lean
attribute [fun_prop] CFC.continuous_abs -- missing attribute
open ContinuousLinearMap in
example {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace ι]
    (a : ι → H →L[ℂ] H) (ha : Continuous a) :
    Continuous (fun i ↦ CFC.sqrt (adjoint (a i) ∘L (a i))) := by
  conv in CFC.sqrt _ => rw [← star_eq_adjoint, ← mul_def, ← CFC.abs]
  fun_prop
```

# Operator topology zoo
%%%
vertical := true
%%%

:::hstack
+ norm: {lean}`@ContinuousLinearMap`
+ strong operator: {lean}`@PointwiseConvergenceCLM`
+ weak operator: {lean}`@ContinuousLinearMapWOT`
+ weak Banach: {lean}`@WeakSpace`
+ others not previously formalized
+ most involve topologies defined via a _predual_

{image "Optop.svg" (height := "100%")}[Operator topologies]
:::

## Preduals, W\*-algebras and von Neumann algebras

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
+ Note that we have both {lean}`WStarAlgebra` and {lean}`VonNeumannAlgebra` in Mathlib, why?
+ Which one should we prefer? Why do we need the abstract approach at all?
+ Main idea behind uniqueness portion of Sakai's theorem.

## Goals for W\*-algebras

> The rabbit-hole went straight on like a tunnel for some way, and then dipped suddenly down,
  so suddenly that Alice had not a moment to think about stopping herself before she found herself
  falling down a very deep well.

+ Develop API for preduals and W\*-algebras, allowing for distinct preduals even though they
  are unique up to isomorphism.
+ Develop the necessary functional analysis, this includes the Krein–Smulian theorem, the bipolar
  theorem and the Mackey–Arens theorem, among others.
+ Construct the various operator topologies (ultraweak, ultrastrong, ultrastrong-\*,
  Arens–Mackey) on W\*-algebras, and establish their inclusions
+ Show that the ultraweak topology on a W\*-algebra makes it into a semitopological star algebra.
+ Prove Sakai's theorem

```lean -show
end
```

# Prerequisites: the _bipolar theorem_
%%%
vertical := true
%%%

```lean -show
open scoped ComplexOrder
open LinearMap.IsWeak
variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (y : F) (s : Set E)
```

Before his untimely death, Christopher Hoskin opened
[#26345](https://github.com/leanprover-community/mathlib4/pull/26345)
which establishes the _bipolar theorem_ for a general bilinear form
{lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`.

*Bipolar theorem*. Let {lean}`E` and {lean}`F` be vector spaces over a field {lean}`𝕜` (either
{lean}`ℝ` or {lean}`ℂ`), and let {lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` be a bilinear form. Moreover,
suppose that {lean}`E` is equipped with the weak topology induced by {lean}`B` (i.e., the weakest
topology such that for every {lean}`(y : F)`, the map {lean}`fun x ↦ B x y` is continuous).
Then, for any nonempty set {lean}`(s : Set E)`, the bipolar of {lean}`s` with respect to {lean}`B`,
is the closed absolutely convex hull of {lean}`s` (i.e.,
{lean +error}`B.flip.polar (B.polar s) = closedAbsConvexHull 𝕜 s`).

## Let's play a game

{lean}`@WeakBilin` is a type synonym for {lean}`E` equipped with the weak topology induced by a
given bilinear form {lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`. What's wrong with the following declaration
(excised directly from Mathlib)?
```lean
example {𝕜 E F : Type*} [TopologicalSpace 𝕜] [CommSemiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (y : F) :
    Continuous fun (x : WeakBilin B) ↦ B x y :=
  WeakBilin.eval_continuous B y
```

:::fragment fadeUp
Abuse of definitional equality occurs when Lean infers that a given term should have type `α` but
we provide a term of type `β`, Lean can verify that these types are definitionally equal (so there
is no type mismatch error), but not at an appropriate transparency level.
:::

:::fragment fadeUp
Note: {lean}`@WeakBilin` not only has defeq abuse, but is also missing quite a bit of API including,
for example, the barrier-preserving equivalence between {lean}`E` and {lean}`WeakBilin B`.
:::

## Fixing the defeq abuse

Using {lean}`WeakBilin.pairing B`, we can rephrase the previous lemma to avoid defeq abuse:
```lean
example {𝕜 E F : Type*} [TopologicalSpace 𝕜] [CommSemiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (y : F) :
    Continuous fun x ↦ WeakBilin.pairing B x y :=
  WeakBilin.eval_continuous B y
```

:::fragment fadeUp
We can also use it to state the bipolar theorem correctly, but note that it's maybe slightly messy.
There is currently a completed proof of this in
[#26345](https://github.com/leanprover-community/mathlib4/pull/26345)
```lean
open WeakBilin ComplexOrder in
example {𝕜 E F : Type*} [TopologicalSpace 𝕜] [RCLike 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set (WeakBilin B)) :
    (pairing B).flip.polar ((pairing B).polar s) =
      closedAbsConvexHull 𝕜 s := by
  sorry
```
:::

## More synonyms!

Other types are further synonyms layered atop {lean}`@WeakBilin`.
including {lean}`@WeakDual`, {lean}`@WeakSpace` and {lean}`Ultraweak`.
Each of these would need to have its own bipolar theorem.

:::fragment fadeUp
Avoid it by abstracting! We introduced a class {lean}`@LinearMap.IsWeak` which encodes the fact
that a given bilinear map induces the existing topology on it's domain.
:::

:::fragment fadeUp
+ This allows for: a bipolar theorem {lean}`@LinearMap.bipolar` that is simultaneously parameterized
  over all the above weak type variations above.
+ It's not just for bipolar the theorem, but in fact *any* situation where you want to refer to a
  generic weak topology.
:::

# The Mackey–Arens theorem and polar topologies
%%%
vertical := true
%%%
```lean -show
section
variable (𝔖 : WeakBilin B.flip)
```

*Polar topology.* Suppose {lean}`(B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` is a bilinear form, and {lean}`F` is
equipped with the weak topology induced by {lean}`B.flip`. If {lean}`𝔖` is a collection of
_von Neumann bounded_ subset of {lean}`F`, then the _polar topology_ on {lean}`E` induced by
{lean}`B` and {lean}`𝔖` is the (pullback of) topology of uniform convergence on the sets in
{lean}`𝔖`.

:::fragment fadeUp
In order to discuss von Neumann boundedness, our sets must be in a type with a topology.
```lean
#check 𝔖
```
:::

:::fragment fadeUp
```lean -show
variable [TopologicalSpace F]
```
Again, {lean}`@LinearMap.IsWeak` allows us to be more general, and instead paramterize over any
type `F` (with an existing topology) such that {lean}`B.flip.IsWeak` is satisfied.
:::

```lean -show
end
```

## The Mackey topology

```lean -show
variable [TopologicalSpace E] [TopologicalSpace F]
```

The _Mackey topology_ (corresponding to the bilinear form {lean}`B` satisfying
{lean}`B.flip.IsWeak`) is the polar topology corresponding to all compact (absolutely) convex
subsets of {lean}`F`. This is {lean}`@Mackey`

:::fragment fadeUp
*Compatible dual pairings.* A bilinear form {lean}`B` is _compatible_
({lean}`@LinearMap.IsCompatible`) with an existing topology on {lean}`E` if {lean}`B.flip` is an
isomorphism onto {lean}`StrongDual 𝕜 E` (appropriately interpreted).
:::

:::fragment fadeUp
*Mackey–Arens theorem.* Suppose {lean}`B` is a compatible bilinear form where {lean}`E` is a locally
convex topological vector space. Then the Mackey topology corresponding to {lean}`B` is finer
than the pre-existing locally convex topology on {lean}`E`. Conversely, any topology finer than the
weak topology induced by {lean}`B` and coarser than the Mackey topology induced by {lean}`B` is
compatible with {lean}`B`.

We proved the hard direction in {lean}`@continuous_ofMackey`
:::

# Other things we've managed

+ The {lean}`@krein_smulian` theorem and a submodule variant {lean}`@krein_smulian_of_submodule`
+ The definitions of {lean}`PositiveContinuousLinearMap`, {lean}`Ultraweak`, and a new
  order-theoretic type class {lean}`ConditionallyCompletePartialOrderSup` for which we construct
  an instance for {lean}`Ultraweak`.
+ ultraweakly continuous positive linear functionals separate points and are _normal_ (i.e., they
  satisfy a monotone convergence property).
+ The definition of {lean}`IsSemitopologicalRing` and related topics.

# Some takeaways

+ The theory of W\*-algebras requires *significantly* more abstract functional analysis than the
  theory of C\*-algebras.
+ It always takes longer than you think to do it right,
  even if you already understand this principle.
+ Mathematicians are sloppy (I count myself here).
+ Formalization provides new insights that are otherwise hard to glean.
+ avoid dependent types and unbundle where possible
+ avoid data entirely if possible
+ always be on the lookout for unifying abstractions
