module

public import LeanOA.Predual

public section

@[expose]
def Ultrastrong (𝕜 M P : Type*) [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P] := M

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedRing M] [StarRing M] [NormedAlgebra 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

variable (𝕜 M P) in
/-- The canonical map from `M` to `Ultrastrong 𝕜 M P`. -/
@[expose] def toUltrastrong (x : M) : Ultrastrong 𝕜 M P := x

/-- The canonical map from `Ultrastrong 𝕜 M P` to `M`. -/
@[expose] def Ultrastrong.ofUltrastrong (x : Ultrastrong 𝕜 M P) : M := x

namespace Ultrastrong

@[simp] lemma toUltrastrong_ofUltrastrong (x : Ultrastrong 𝕜 M P) :
    toUltrastrong 𝕜 M P x.ofUltrastrong = x := rfl

@[simp] lemma ofUltrastrong_toUltrastrong (x : M) :
    (toUltrastrong 𝕜 M P x).ofUltrastrong = x := rfl

variable (𝕜 M P) in
/-- The canonical equivalence between `Ultrastrong 𝕜 M P` and `M`. -/
@[expose, simps] def equiv : Ultrastrong 𝕜 M P ≃ M where
  toFun := ofUltrastrong
  invFun := toUltrastrong 𝕜 M P

instance : AddCommGroup (Ultrastrong 𝕜 M P) := equiv 𝕜 M P |>.addCommGroup
instance : Module 𝕜 (Ultrastrong 𝕜 M P) := equiv 𝕜 M P |>.module 𝕜

@[simp] lemma toUltrastrong_add (x y : M) :
    toUltrastrong 𝕜 M P (x + y) = toUltrastrong 𝕜 M P x + toUltrastrong 𝕜 M P y := rfl

@[simp] lemma ofUltrastrong_add (x y : Ultrastrong 𝕜 M P) :
    (x + y).ofUltrastrong = x.ofUltrastrong + y.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_smul (a : 𝕜) (x : M) :
    toUltrastrong 𝕜 M P (a • x) = a • toUltrastrong 𝕜 M P x := rfl

@[simp] lemma ofUltrastrong_smul (a : 𝕜) (x : Ultrastrong 𝕜 M P) :
    (a • x).ofUltrastrong = a • x.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_zero : toUltrastrong 𝕜 M P (0 : M) = 0 := rfl
@[simp] lemma ofUltrastrong_zero : (0 : Ultrastrong 𝕜 M P).ofUltrastrong = 0 := rfl

@[simp] lemma toUltrastrong_neg (x : M) :
    toUltrastrong 𝕜 M P (-x) = -toUltrastrong 𝕜 M P x := rfl

@[simp] lemma ofUltrastrong_neg (x : Ultrastrong 𝕜 M P) :
    (-x).ofUltrastrong = -x.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_sub (x y : M) :
    toUltrastrong 𝕜 M P (x - y) = toUltrastrong 𝕜 M P x - toUltrastrong 𝕜 M P y := rfl

@[simp] lemma ofUltrastrong_sub (x y : Ultrastrong 𝕜 M P) :
    (x - y).ofUltrastrong = x.ofUltrastrong - y.ofUltrastrong := rfl

@[simp] lemma toUltrastrong_inj {x y : M} :
    toUltrastrong 𝕜 M P x = toUltrastrong 𝕜 M P y ↔ x = y :=
  equiv 𝕜 M P |>.symm.injective.eq_iff

@[simp] lemma ofUltrastrong_inj {x y : Ultrastrong 𝕜 M P} :
    x.ofUltrastrong = y.ofUltrastrong ↔ x = y :=
  equiv 𝕜 M P |>.injective.eq_iff

@[simp] lemma toUltrastrong_eq_zero {x : M} : toUltrastrong 𝕜 M P x = 0 ↔ x = 0 :=
  toUltrastrong_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ toUltrastrong_inj

@[simp] lemma ofUltrastrong_eq_zero {x : Ultrastrong 𝕜 M P} : x.ofUltrastrong = 0 ↔ x = 0 :=
  ofUltrastrong_zero (𝕜 := 𝕜) (M := M) (P := P) ▸ ofUltrastrong_inj

end Ultrastrong
