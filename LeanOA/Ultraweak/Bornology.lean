module

public import LeanOA.Ultraweak.Basic

@[expose] public section

variable {𝕜 M P : Type*} [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

namespace Ultraweak

open Bornology

/-- The bornology on `σ(M, P)_𝕜` is the one induced by the norm on `M`. -/
instance : Bornology (σ(M, P)_𝕜) := inferInstanceAs (Bornology M)

@[simp]
lemma isBounded_preimage_ofUltraweak {s : Set M} :
    IsBounded (ofUltraweak ⁻¹' s : Set (σ(M, P)_𝕜)) ↔ IsBounded s :=
  Iff.rfl

@[simp]
lemma isBounded_preimage_toUltraweak {s : Set (σ(M, P)_𝕜)} :
    IsBounded (toUltraweak 𝕜 P ⁻¹' s : Set M) ↔ IsBounded s :=
  Iff.rfl

@[simp]
lemma isBounded_image_ofUltraweak {s : Set (σ(M, P)_𝕜)} :
    IsBounded (ofUltraweak '' s : Set M) ↔ IsBounded s :=
  linearEquiv 𝕜 M P |>.image_eq_preimage_symm s ▸ isBounded_preimage_toUltraweak

@[simp]
lemma isBounded_image_toUltraweak {s : Set M} :
    IsBounded (toUltraweak 𝕜 P '' s : Set (σ(M, P)_𝕜)) ↔ IsBounded s :=
  linearEquiv 𝕜 M P |>.symm.image_eq_preimage_symm s ▸ isBounded_preimage_ofUltraweak

end Ultraweak
