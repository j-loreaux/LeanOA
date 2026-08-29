import LeanOABlueprint.Base
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanOABlueprint.Chapters.WStarAlgebrasAndTopologies
import LeanOABlueprint.Chapters.OrderLemmas
import LeanOABlueprint.Chapters.ProjectionLemmas
import LeanOABlueprint.Chapters.PositiveFunctionalsAndStates
import LeanOABlueprint.Chapters.StoneanSpacesAndMasas
import LeanOABlueprint.Chapters.NormalityAndUltraweakContinuity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "WStarAlgebras have Unique Preduals" =>

This is the blueprint of [LeanOA](https://github.com/j-loreaux/LeanOA), a formalization of
operator algebra theory in Lean 4, built on top of
[Mathlib](https://github.com/leanprover-community/mathlib4). Its target is the theorem that a
$`W^*`-algebra has a unique predual, along with the $`C^*`/$`W^*`-algebra, locally convex,
and ultraweak-topology infrastructure that goal needs.

The numbering of the results below follows Sakai's *C\*-Algebras and W\*-Algebras*.

{include 0 LeanOABlueprint.Chapters.WStarAlgebrasAndTopologies}
{include 0 LeanOABlueprint.Chapters.OrderLemmas}
{include 0 LeanOABlueprint.Chapters.ProjectionLemmas}
{include 0 LeanOABlueprint.Chapters.PositiveFunctionalsAndStates}
{include 0 LeanOABlueprint.Chapters.StoneanSpacesAndMasas}
{include 0 LeanOABlueprint.Chapters.NormalityAndUltraweakContinuity}

{blueprint_graph}
{blueprint_summary}
