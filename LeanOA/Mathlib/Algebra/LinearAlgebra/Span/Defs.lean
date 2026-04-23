module

public import Mathlib.LinearAlgebra.Span.Defs

public section CommuteSpan

variable {R M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring M] [Module R M]
  [IsScalarTower R M M] [SMulCommClass R M M]

/-- If every element of a set `s` commutes with `x`, then every element of `Submodule.span R s`
commutes with `x`. -/
theorem Commute.span_left {s : Set M} {x : M} (h : ∀ y ∈ s, Commute y x) :
    ∀ y ∈ Submodule.span R s, Commute y x := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem _ _ => aesop
  | zero => exact Commute.zero_left _
  | add _ _ _ _ h₁ h₂ => exact h₁.add_left h₂
  | smul _ _ _ h => exact h.smul_left _

/-- If every element of a set `s` commutes with `x`, then every element of `Submodule.span R s`
commutes with `x`. -/
theorem Commute.span_right {s : Set M} {x : M} (h : ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Submodule.span R s, Commute x y := by
  simp only [Commute.symm_iff (a := x)] at *
  exact Commute.span_left h

end CommuteSpan
