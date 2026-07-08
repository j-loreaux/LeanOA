module

public import Mathlib.Topology.Bornology.Basic

@[expose] public section

open Bornology

theorem Bornology.IsBounded.disjoint_cobounded_of_mem {α : Type*} [Bornology α]
    {l : Filter α} {s : Set α} (hs : IsBounded s) (hl : s ∈ l) :
    Disjoint l (cobounded α) :=
  l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩
