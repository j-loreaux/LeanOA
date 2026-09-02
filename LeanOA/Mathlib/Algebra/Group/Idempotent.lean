module

public import Mathlib.Algebra.Group.Idempotent

@[expose] public section

lemma IsIdempotentElem.idempotent_mul_mul {M : Type*} [Semigroup M] {e : M}
    (he : IsIdempotentElem e) :
    (e * · * e) ∘ (e * · * e) = (e * · * e) := by
  ext; simp [mul_assoc, he.mul_mul_self, he.mul_self_mul]
