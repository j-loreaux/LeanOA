import Mathlib.Data.Set.Function

namespace Set

variable {α β γ : Type*} {s : Set α} {f₁ f₂ : α → β} {a : α}

/-- This lemma exists for use by `aesop` as a forward rule. -/
@[aesop safe forward]
lemma EqOn.eq_of_mem (h : s.EqOn f₁ f₂) (ha : a ∈ s) : f₁ a = f₂ a :=
  h ha

end Set
