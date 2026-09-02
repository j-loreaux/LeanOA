import Verso
import VersoManual
import VersoBlueprint

-- The formalization itself. Blueprint statements refer to its declarations through
-- `(lean := "...")`, which resolves names in the environment of the chapter module, so the
-- chapters need these imports to be in scope.
import LeanOA

-- Mathlib modules providing declarations that the blueprint cites but that LeanOA does not
-- itself depend on.
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Topology.Homeomorph.Lemmas

open Informal

/-
TeX macros shared by every chapter.

Blueprint math is rendered by KaTeX rather than by a full LaTeX engine, so the macro
vocabulary of the old `blueprint/src/macros/common.tex` cannot be replayed verbatim.  The
only project macros defined there were `\spectrum` and `\quasispectrum`, both of which took
a LaTeX *optional* argument (`\newcommand{\spectrum}[2][]{...}`).  KaTeX's `\newcommand`
has no optional-argument form, so they are re-expressed below as ordinary two-argument
macros; write `\spectrum{}{a}` for an unadorned spectrum.

`\providecommand` is used throughout so that a name KaTeX already ships wins over the local
definition instead of raising a redefinition error.
-/
tex_prelude
  r#"\providecommand{\spectrum}[2]{\sigma_{#1}(#2)}
\providecommand{\quasispectrum}[2]{\sigma'_{#1}(#2)}"#
