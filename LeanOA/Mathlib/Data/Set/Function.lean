module

public import Mathlib.Data.Set.Function
public import Mathlib.Tactic.TermCongr

@[expose] public section

open Set

/-- If `f` is an idempotent function which maps sets `s` and `t` to themselves, then
`f '' (s ∩ t) = (f '' s) ∩ t`. -/
lemma Set.MapsTo.image_inter_of_idempotent {α : Type*} {s t : Set α} {f : α → α}
    (hf : f ∘ f = f) (hfs : MapsTo f s s) (hft : MapsTo f t t) :
    f '' (s ∩ t) = (f '' s) ∩ t := by
  apply subset_antisymm (fun _ _ ↦ by aesop)
  rintro - ⟨⟨x, hx, rfl⟩, hxt⟩
  exact ⟨f x, ⟨hfs hx, hxt⟩, congr($hf x)⟩
