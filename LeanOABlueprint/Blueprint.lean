import LeanOABlueprint.Base
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanOABlueprint.Chapters.DualPairsAndWeakTopologies
import LeanOABlueprint.Chapters.WStarAlgebrasAndTopologies
import LeanOABlueprint.Chapters.OrderLemmas
import LeanOABlueprint.Chapters.ProjectionLemmas
import LeanOABlueprint.Chapters.PositiveFunctionalsAndStates
import LeanOABlueprint.Chapters.StoneanSpacesAndMasas
import LeanOABlueprint.Chapters.NormalityAndUltraweakContinuity
import LeanOABlueprint.Chapters.UnitalityAndOtherTopologies

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
The final chapter collects parts of Sakai's development (unitality of $`W^*`-algebras, and the
Mackey and strong topologies) that the proof of the main theorem does not need.

{include 0 LeanOABlueprint.Chapters.DualPairsAndWeakTopologies}
{include 0 LeanOABlueprint.Chapters.WStarAlgebrasAndTopologies}
{include 0 LeanOABlueprint.Chapters.OrderLemmas}
{include 0 LeanOABlueprint.Chapters.ProjectionLemmas}
{include 0 LeanOABlueprint.Chapters.PositiveFunctionalsAndStates}
{include 0 LeanOABlueprint.Chapters.StoneanSpacesAndMasas}
{include 0 LeanOABlueprint.Chapters.NormalityAndUltraweakContinuity}
{include 0 LeanOABlueprint.Chapters.UnitalityAndOtherTopologies}

{blueprint_graph}
{blueprint_summary}
