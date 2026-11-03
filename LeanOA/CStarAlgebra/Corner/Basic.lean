module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Idempotents

@[expose] public section

/-! # The corner of a star projection

If `p` is a star projection in a (possibly non-unital) star ring `A`, then the *corner*
`p * A * p` is a unital star ring with unit `p`. Following `IsIdempotentElem.Corner`, we realize
it as a type `hp.Corner` depending on the proof `hp : IsStarProjection p`. Because `hp` appears
in the type, all of the structure on the corner can be provided by instances, and the unit is
`p` *by definition*. In particular, when `A` is a (non-unital) C⋆-algebra, `hp.Corner` is a
(unital) C⋆-algebra.

## Main declarations

+ `IsStarProjection.Corner`: the corner `p * A * p` of a star projection `p`.
+ `IsStarProjection.Corner.mk`: an element `x : A` with `p * x * p = x`, as an element of the
  corner.
+ `IsStarProjection.Corner.subtype`: the inclusion of the corner as a non-unital star algebra
  homomorphism.
+ `IsStarProjection.toCorner`: the compression `x ↦ p * x * p` as a linear map onto the corner.
-/

variable {R A : Type*}

namespace IsStarProjection

set_option linter.unusedVariables false in
/-- The corner associated to a star projection `p` in a star ring without `1` is the star ring
with `p` as `1` consisting of all elements of the form `p * x * p`. -/
@[nolint unusedArguments]
def Corner [Semigroup A] [Star A] {p : A} (hp : IsStarProjection p) : Type _ :=
  Subsemigroup.corner p

namespace Corner

section Semigroup

variable [Semigroup A] [Star A] {p : A} {hp : IsStarProjection p}

/-- The underlying element of `A` of an element of the corner. -/
@[coe]
def val (x : hp.Corner) : A := Subtype.val x

instance : CoeOut hp.Corner A := ⟨val⟩

@[ext]
lemma ext {x y : hp.Corner} (h : (x : A) = y) : x = y := Subtype.ext h

lemma coe_injective : Function.Injective ((↑) : hp.Corner → A) := Subtype.val_injective

@[simp, norm_cast]
lemma coe_inj {x y : hp.Corner} : (x : A) = y ↔ x = y := coe_injective.eq_iff

@[simp]
lemma mul_coe_eq (x : hp.Corner) : p * x = x :=
  (Subsemigroup.mem_corner_iff hp.isIdempotentElem |>.mp x.2).1

@[simp]
lemma coe_mul_eq (x : hp.Corner) : x * p = x :=
  (Subsemigroup.mem_corner_iff hp.isIdempotentElem |>.mp x.2).2

lemma mul_coe_mul_eq (x : hp.Corner) : p * x * p = x := by
  rw [mul_coe_eq, coe_mul_eq]

variable (hp) in
/-- An element `x : A` with `p * x * p = x`, regarded as an element of the corner. -/
def mk (x : A) (hx : p * x * p = x) : hp.Corner := ⟨x, x, hx⟩

@[simp]
lemma coe_mk (x : A) (hx : p * x * p = x) : (mk hp x hx : A) = x := rfl

@[simp]
lemma mk_coe (x : hp.Corner) : mk hp x (mul_coe_mul_eq x) = x := rfl

lemma mem_range_coe_iff {x : A} : x ∈ Set.range ((↑) : hp.Corner → A) ↔ p * x * p = x :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ mul_coe_mul_eq y, fun hx ↦ ⟨mk _ x hx, rfl⟩⟩

lemma range_coe : Set.range ((↑) : hp.Corner → A) = {x | p * x * p = x} :=
  Set.ext fun _ ↦ mem_range_coe_iff

end Semigroup

section NonUnitalSemiring

variable [NonUnitalSemiring A] [StarRing A] {p : A} {hp : IsStarProjection p}

/-! We construct the algebraic structure on the corner by hand, rather than transferring it from
`IsIdempotentElem.Corner`, so that all of the data is of the form `mk hp (f ↑x) _`. In particular,
`nsmul` and `zsmul` agree with the `SMul R hp.Corner` instance (for `R := ℕ` or `R := ℤ`) at
instance reducible transparency, so that there are no `Module ℕ` or `Module ℤ` diamonds. -/

instance : Zero hp.Corner where
  zero := mk hp 0 (by simp)

instance : One hp.Corner where
  one := mk hp p (by simp only [hp.isIdempotentElem.eq])

instance : Add hp.Corner where
  add x y := mk hp (x + y) (by simp only [mul_add, add_mul, mul_coe_mul_eq])

instance : Mul hp.Corner where
  mul x y := mk hp (x * y) (by rw [← mul_assoc, mul_coe_eq, mul_assoc, coe_mul_eq])

instance : NatCast hp.Corner where
  natCast n := mk hp (n • p) <| by
    rw [mul_smul_comm, smul_mul_assoc, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]

lemma mul_star_coe_mul_eq (x : hp.Corner) : p * star (x : A) * p = star (x : A) := by
  nth_rw 2 [← mul_coe_mul_eq x]
  simp only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]

instance : Star hp.Corner where
  star x := mk hp (star (x : A)) (mul_star_coe_mul_eq x)

section SMul

variable [SMul R A] [IsScalarTower R A A] [SMulCommClass R A A]

lemma mul_smul_coe_mul_eq (r : R) (x : hp.Corner) : p * (r • (x : A)) * p = r • (x : A) := by
  rw [mul_smul_comm, smul_mul_assoc, mul_coe_mul_eq]

instance : SMul R hp.Corner where
  smul r x := mk hp (r • (x : A)) (mul_smul_coe_mul_eq r x)

@[simp, norm_cast]
lemma coe_smul (r : R) (x : hp.Corner) : ((r • x : hp.Corner) : A) = r • (x : A) := rfl

instance : IsScalarTower R hp.Corner hp.Corner where
  smul_assoc r x y := ext <| smul_mul_assoc r (x : A) y

instance : SMulCommClass R hp.Corner hp.Corner where
  smul_comm r x y := ext <| (mul_smul_comm r (x : A) y).symm

instance [Star R] [StarModule R A] : StarModule R hp.Corner where
  star_smul r x := ext <| star_smul r (x : A)

end SMul

instance : NonUnitalSemiring hp.Corner :=
  coe_injective.nonUnitalSemiring _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Semiring hp.Corner where
  one_mul x := ext <| mul_coe_eq x
  mul_one x := ext <| coe_mul_eq x
  natCast_zero := ext <| zero_nsmul p
  natCast_succ n := ext <| succ_nsmul p n

instance : StarRing hp.Corner where
  star_involutive x := ext <| star_star (x : A)
  star_mul x y := ext <| star_mul (x : A) y
  star_add x y := ext <| star_add (x : A) y

@[simp, norm_cast] lemma coe_zero : ((0 : hp.Corner) : A) = 0 := rfl
@[simp] lemma coe_one : ((1 : hp.Corner) : A) = p := rfl
@[simp, norm_cast] lemma coe_add (x y : hp.Corner) : ((x + y : hp.Corner) : A) = x + y := rfl
@[simp, norm_cast] lemma coe_mul (x y : hp.Corner) : ((x * y : hp.Corner) : A) = x * y := rfl
@[simp, norm_cast] lemma coe_star (x : hp.Corner) : ((star x : hp.Corner) : A) = star (x : A) :=
  rfl

@[simp, norm_cast]
lemma coe_nsmul (n : ℕ) (x : hp.Corner) : ((n • x : hp.Corner) : A) = n • (x : A) := rfl

@[simp]
lemma coe_natCast (n : ℕ) : ((n : hp.Corner) : A) = n • p := rfl

@[simp]
lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : hp.Corner) : A) = (ofNat(n) : ℕ) • p :=
  rfl

lemma coe_eq_zero {x : hp.Corner} : (x : A) = 0 ↔ x = 0 := coe_inj (y := 0)

lemma nontrivial_iff : Nontrivial hp.Corner ↔ p ≠ 0 := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, ← subsingleton_iff_zero_eq_one, ne_eq,
    not_not, ← coe_inj, coe_zero, coe_one, eq_comm]

@[simp]
lemma isStarProjection_coe_iff {q : hp.Corner} : IsStarProjection (q : A) ↔ IsStarProjection q := by
  simp only [isStarProjection_iff', ← coe_mul, ← coe_star, coe_inj]

end NonUnitalSemiring

instance [NonUnitalCommSemiring A] [StarRing A] {p : A} {hp : IsStarProjection p} :
    CommSemiring hp.Corner where
  mul_comm x y := ext <| mul_comm (x : A) y

section NonUnitalRing

variable [NonUnitalRing A] [StarRing A] {p : A} {hp : IsStarProjection p}

instance : Neg hp.Corner where
  neg x := mk hp (-x) (by rw [mul_neg, neg_mul, mul_coe_mul_eq])

instance : Sub hp.Corner where
  sub x y := mk hp (x - y) (by simp only [mul_sub, sub_mul, mul_coe_mul_eq])

instance : IntCast hp.Corner where
  intCast n := mk hp (n • p) <| by
    rw [mul_smul_comm, smul_mul_assoc, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]

instance : NonUnitalRing hp.Corner :=
  coe_injective.nonUnitalRing _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Ring hp.Corner where
  __ : Semiring hp.Corner := inferInstance
  __ : NonUnitalRing hp.Corner := inferInstance
  intCast_ofNat n := ext <| natCast_zsmul p n
  intCast_negSucc n := ext <| negSucc_zsmul p n

@[simp, norm_cast] lemma coe_neg (x : hp.Corner) : ((-x : hp.Corner) : A) = -x := rfl
@[simp, norm_cast] lemma coe_sub (x y : hp.Corner) : ((x - y : hp.Corner) : A) = x - y := rfl

@[simp, norm_cast]
lemma coe_zsmul (n : ℤ) (x : hp.Corner) : ((n • x : hp.Corner) : A) = n • (x : A) := rfl

@[simp]
lemma coe_intCast (n : ℤ) : ((n : hp.Corner) : A) = n • p := rfl

end NonUnitalRing

instance [NonUnitalCommRing A] [StarRing A] {p : A} {hp : IsStarProjection p} :
    CommRing hp.Corner where
  mul_comm := mul_comm

section Module

variable [NonUnitalSemiring A] [StarRing A] {p : A} {hp : IsStarProjection p}

instance [Semiring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    Module R hp.Corner where
  one_smul x := ext <| one_smul R (x : A)
  mul_smul r s x := ext <| mul_smul r s (x : A)
  smul_zero r := ext <| smul_zero (A := A) r
  smul_add r x y := ext <| smul_add r (x : A) y
  add_smul r s x := ext <| add_smul r s (x : A)
  zero_smul x := ext <| zero_smul R (x : A)

variable [CommSemiring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

instance : Algebra R hp.Corner := .ofModule smul_mul_assoc mul_smul_comm

lemma coe_algebraMap (r : R) : (algebraMap R hp.Corner r : A) = r • p := rfl

variable (R hp) in
/-- The inclusion of the corner `p * A * p` into `A`, as a non-unital star algebra
homomorphism. -/
def subtype : hp.Corner →⋆ₙₐ[R] A where
  toFun := (↑)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
lemma coe_subtype : ⇑(subtype R hp) = (↑) := rfl

lemma subtype_injective : Function.Injective (subtype R hp) := coe_injective

end Module

end Corner

section toCorner

variable [NonUnitalSemiring A] [StarRing A] [CommSemiring R] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] {p : A}

variable (R) in
/-- The compression `x ↦ p * x * p` onto the corner of a star projection `p`, as a linear map. -/
def toCorner (hp : IsStarProjection p) : A →ₗ[R] hp.Corner where
  toFun x := Corner.mk hp (p * x * p) <| by
    simp only [← mul_assoc, hp.isIdempotentElem.eq]
    rw [mul_assoc _ p p, hp.isIdempotentElem.eq]
  map_add' x y := Corner.ext <| show p * (x + y) * p = p * x * p + p * y * p by
    simp [mul_add, add_mul]
  map_smul' r x := Corner.ext <| show p * (r • x) * p = r • (p * x * p) by
    simp [mul_smul_comm, smul_mul_assoc]

variable (hp : IsStarProjection p)

@[simp]
lemma coe_toCorner (x : A) : (hp.toCorner R x : A) = p * x * p := rfl

@[simp]
lemma toCorner_coe (x : hp.Corner) : hp.toCorner R x = x :=
  Corner.ext <| Corner.mul_coe_mul_eq x

lemma toCorner_surjective : Function.Surjective (hp.toCorner R) :=
  fun x ↦ ⟨x, toCorner_coe hp x⟩

@[simp]
lemma toCorner_star (x : A) : hp.toCorner R (star x) = star (hp.toCorner R x) :=
  Corner.ext <| by simp [mul_assoc, hp.isSelfAdjoint.star_eq]

end toCorner

section cornerSubmodule

variable [NonUnitalSemiring A] [StarRing A] [CommSemiring R] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] {p : A}

variable (R) in
/-- The corner `p * A * p` of a star projection `p`, as a submodule of `A`. This is the range of
`IsStarProjection.Corner.subtype`, and it is linearly equivalent to `hp.Corner` via
`IsStarProjection.cornerLinearEquiv`. -/
@[nolint unusedArguments]
def cornerSubmodule (_ : IsStarProjection p) : Submodule R A where
  carrier := {x | p * x * p = x}
  zero_mem' := by simp
  add_mem' {x y} (hx : p * x * p = x) (hy : p * y * p = y) :=
    show p * (x + y) * p = x + y by rw [mul_add, add_mul, hx, hy]
  smul_mem' r x (hx : p * x * p = x) :=
    show p * (r • x) * p = r • x by rw [mul_smul_comm, smul_mul_assoc, hx]

variable (hp : IsStarProjection p)

lemma mem_cornerSubmodule {x : A} : x ∈ hp.cornerSubmodule R ↔ p * x * p = x := .rfl

lemma coe_cornerSubmodule :
    (hp.cornerSubmodule R : Set A) = Set.range ((↑) : hp.Corner → A) :=
  Corner.range_coe.symm

lemma coe_mem_cornerSubmodule (x : hp.Corner) : (x : A) ∈ hp.cornerSubmodule R :=
  Corner.mul_coe_mul_eq x

lemma coe_cornerSubmodule_eq_range_mul_mul :
    (hp.cornerSubmodule R : Set A) = Set.range (p * · * p) := by
  ext x
  refine ⟨fun hx ↦ ⟨x, (hp.mem_cornerSubmodule (R := R)).mp hx⟩, ?_⟩
  rintro ⟨y, rfl⟩
  simpa using hp.coe_mem_cornerSubmodule (R := R) (hp.toCorner R y)

variable (R) in
/-- The corner `hp.Corner` is linearly equivalent to the submodule `hp.cornerSubmodule R`. -/
def cornerLinearEquiv : hp.Corner ≃ₗ[R] hp.cornerSubmodule R where
  toFun x := ⟨x, coe_mem_cornerSubmodule hp x⟩
  invFun x := Corner.mk hp x x.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma coe_cornerLinearEquiv_apply (x : hp.Corner) : (hp.cornerLinearEquiv R x : A) = x := rfl

@[simp]
lemma coe_cornerLinearEquiv_symm_apply (x : hp.cornerSubmodule R) :
    ((hp.cornerLinearEquiv R).symm x : A) = x :=
  rfl

end cornerSubmodule

namespace Corner

section Normed

variable [NonUnitalNormedRing A] [StarRing A] {p : A} {hp : IsStarProjection p}

variable (hp) in
/-- The inclusion of the corner into `A`, as a non-unital ring homomorphism. This is an auxiliary
definition used to construct the normed ring structure; use `IsStarProjection.Corner.subtype`
instead. -/
def coeNonUnitalRingHom : hp.Corner →ₙ+* A where
  toFun := (↑)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable instance : NormedRing hp.Corner where
  __ : Ring hp.Corner := inferInstance
  __ := NonUnitalNormedRing.induced hp.Corner A (coeNonUnitalRingHom hp) coe_injective

@[simp, norm_cast]
lemma norm_coe (x : hp.Corner) : ‖(x : A)‖ = ‖x‖ := rfl

@[simp, norm_cast]
lemma nnnorm_coe (x : hp.Corner) : ‖(x : A)‖₊ = ‖x‖₊ := rfl

lemma isometry_coe : Isometry ((↑) : hp.Corner → A) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

instance [CStarRing A] : CStarRing hp.Corner where
  norm_mul_self_le x := CStarRing.norm_mul_self_le (x : A)

lemma isClosed_range_coe : IsClosed (Set.range ((↑) : hp.Corner → A)) := by
  rw [range_coe]
  exact isClosed_eq (by fun_prop) continuous_id

instance [CompleteSpace A] : CompleteSpace hp.Corner :=
  (completeSpace_iff_isComplete_range (f := ((↑) : hp.Corner → A))
    isometry_coe.isUniformInducing).mpr isClosed_range_coe.isComplete

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
    [SMulCommClass 𝕜 A A] : NormedAlgebra 𝕜 hp.Corner where
  norm_smul_le r x := norm_smul_le r (x : A)

end Normed

end Corner

section Normed

variable [NonUnitalNormedRing A] [StarRing A] {p : A} (hp : IsStarProjection p)

lemma isClosed_cornerSubmodule {R : Type*} [CommSemiring R] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : IsClosed (hp.cornerSubmodule R : Set A) :=
  hp.coe_cornerSubmodule (R := R) ▸ Corner.isClosed_range_coe

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
  [SMulCommClass 𝕜 A A]

/-- The corner `hp.Corner` is linearly isometrically equivalent to the submodule
`hp.cornerSubmodule 𝕜`. -/
def cornerLinearIsometryEquiv : hp.Corner ≃ₗᵢ[𝕜] hp.cornerSubmodule 𝕜 where
  __ := hp.cornerLinearEquiv 𝕜
  norm_map' _ := rfl

@[simp]
lemma coe_cornerLinearIsometryEquiv_apply (x : hp.Corner) :
    (hp.cornerLinearIsometryEquiv 𝕜 x : A) = x :=
  rfl

@[simp]
lemma coe_cornerLinearIsometryEquiv_symm_apply (x : hp.cornerSubmodule 𝕜) :
    ((hp.cornerLinearIsometryEquiv 𝕜).symm x : A) = x :=
  rfl

end Normed

namespace Corner

/-- The corner `p * A * p` of a non-unital C⋆-algebra is a C⋆-algebra with unit `p`. -/
noncomputable instance instCStarAlgebra [NonUnitalCStarAlgebra A] {p : A}
    {hp : IsStarProjection p} : CStarAlgebra hp.Corner where

end Corner

end IsStarProjection
