module

public import Mathlib.Data.Real.Archimedean


@[expose] public section

namespace Real
variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}

lemma _root_.Real.sSup_image_nonneg {α : Type*} {f : α → ℝ} {s : Set α} (h : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ sSup (f '' s) := by
  apply Real.sSup_nonneg
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

end Real
