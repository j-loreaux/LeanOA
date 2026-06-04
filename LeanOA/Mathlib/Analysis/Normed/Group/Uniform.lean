module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Uniform

@[expose] public section

open Bornology

@[to_additive isBounded_norm_iff]
lemma isBounded_norm_iff' {E : Type*} [SeminormedGroup E] {s : Set E} :
    IsBounded ((‖·‖) '' s) ↔ IsBounded s := by
  refine ⟨fun hs ↦ ?_, lipschitzWith_one_norm'.isBounded_image⟩
  rw [isBounded_iff_forall_norm_le']
  rw [isBounded_iff_bddBelow_bddAbove] at hs
  simpa [BddAbove, upperBounds] using hs.2

alias ⟨IsBounded.of_norm', IsBounded.norm'⟩ := isBounded_norm_iff'

attribute [to_additive IsBounded.of_norm] IsBounded.of_norm'
attribute [to_additive IsBounded.norm] IsBounded.norm'
