# Scope and unsupported features of the `cfc_pull` tactic

* **Recursing under a binder** (`cfc_sum`, `cfc_apply_pi`) — for which there is a good workaround,
  so this may never need doing.

  **The workaround.** `conv` can go under the binder, and once there the bound variable is an
  ordinary local hypothesis and `cfc_pull` is an ordinary pull:

  ```lean
  example (ha : p a) (hg : ∀ i, ContinuousOn (g i) (spectrum R a)) :
      ∑ i ∈ s, star (cfc (g i) a) = cfc (∑ i ∈ s, fun x ↦ star (g i x)) a := by
    conv_lhs => enter [2, i]; cfc_pull R a
    cfc_pull +defer R a
  ```

  The first line pulls each summand to `cfc (fun x ↦ star (g i x)) a`; the second lets `cfc_sum`
  collect them. (`enter [2, i]`, not `ext i`: `conv` must enter `Finset.sum`'s function argument
  before it can go under the lambda.) This leaves the side goal
  `∀ i ∈ s, ContinuousOn (fun x ↦ star (g i x)) (spectrum R a)`.

  **What a built-in version would take.**

  1. *Matching.* The placeholder would have to be function-valued, `?b : ι → A`, so that the
     pattern reads `∑ i ∈ s, ?b i`. But `abstractHoles` currently uses an element metavariable.
  2. *Recursion.* `pull` would have to run under `withLocalDecl i : ι` and return a family
     `f : ι → R → R` with a pointwise proof, rather than a single function and a single
     equation. Side goals raised under the binder would have to be generalised over `i` before
     being handed back, and `Result` would have to carry the binder.

* **Compositions that also change the scalar ring.**
  `cfc_comp_re : cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A)` is a composition that changes the
  scalar ring from `ℝ` to `ℂ` on the way. The attribute now rejects lemmas like this.
  Supporting them is doable though: give `ComposeLemma` a source and a target ring
  key instead of one `ring`, index and filter `pullExisting`'s loop on the source key, and let
  the `pull newE want` that already follows every composition step do the conversion.

* **Descending through a homomorphism into another algebra.** A `pull` run fixes one algebra and
  one element for its whole duration (`Context.alg`, `Context.elem`). So `StarAlgHom.map_cfc`,
  `Unitization.complex_cfcₙ_eq_cfc_inr` and `cfc_eq_cfc_transfer` are usable only in the
  degenerate, hole-free direction: `φ (cfc f a)` is pulled towards `cfc f (φ a)`, but
  `φ (star a * a)` is not, because that needs the sub-pull `star a * a = cfc _ a` to run in the
  *domain*. Doing it in general means making the algebra and the element part of the mode and
  threading a per-node `Context`, at which point `map_cfc` becomes a `Compose`-like lemma that
  relates two different algebras. That is a substantially bigger change than the ring-changing
  composition above, and the same remark applies to `cfc_map_prod`/`cfc_map_pi`, where the
  components additionally live at *different* elements of *different* algebras.
