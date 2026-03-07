import Mathlib.Topology.Bornology.Basic

open Bornology

theorem Filter.disjoint_cobounded_iff {α : Type*} [Bornology α] {l : Filter α} :
    Disjoint l (cobounded α) ↔ ∃ s ∈ l, Bornology.IsBounded s :=
  l.basis_sets.disjoint_cobounded_iff

alias ⟨Bornology.exists_isBounded_of_disjoint, _⟩ := Filter.disjoint_cobounded_iff

theorem Bornology.IsBounded.disjoint_cobounded_of_mem {α : Type*} [Bornology α]
    {l : Filter α} {s : Set α} (hs : IsBounded s) (hl : s ∈ l) :
    Disjoint l (cobounded α) :=
  l.disjoint_cobounded_iff.mpr ⟨s, hl, hs⟩
