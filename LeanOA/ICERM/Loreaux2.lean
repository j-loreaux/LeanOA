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
