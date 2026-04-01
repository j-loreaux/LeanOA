import Mathlib.Analysis.Normed.Module.WeakDual

/-
Now I have to put together some variables for this. We want an abstract
dual set up. What precisely does this mean?

If we have a pair of vector spaces over a field, and a bilinear form
that separates the points of V. What would it mean to say that a linear
topology on V "has dual space F"? Would it mean that there is a linear
equivalence between F and `V →L[𝕜] 𝕜`? I'm not even sure what that would mean.
There would, perhaps, have to be a coercion of this from continuous linear
maps...forgetting down to a linear space of linear maps. Or maybe there
is already an obvious 𝕜-linear space structure on the whole thing.

Let's try to figure out what is meant by this here...keeping local convexity at
bay as long as possible.
-/

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [AddCommMonoid V] [Module 𝕜 V]
variable [TopologicalSpace V]

#check V →ₗ[𝕜] 𝕜
#synth AddCommGroup (V →ₗ[𝕜] 𝕜)
#synth Module 𝕜 (V →ₗ[𝕜] 𝕜)
#check V →L[𝕜] 𝕜
#synth AddCommMonoid (V →L[𝕜] 𝕜)
#synth Module 𝕜 (V →L[𝕜] 𝕜)

/-
So, it seems there is a natural vector space structure on this. It seems
that this has already incorporated the topology. Let's try to make up the dual
space.
-/

variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F] (b : F →ₗ[𝕜] V →ₗ[𝕜] 𝕜)

def Φ : F → (V →ₗ[𝕜] 𝕜) := fun f ↦ b f

/-
This is kind of funny. There is an easy way to make a linear function on V from an
element of f, given a bilinear form. This thing isn't any sort of equivalence.
We can assume there is a linear equivalence from `F` onto `V →L[𝕜] 𝕜`. So somehow
this gives us a map from the continuous dual into the algebraic dual. Note, it isn't
onto by any means. We may have it injective if the points are separated by F.

Maybe this is essential...
-/
